// ==UserScript==
// @name         SimCompanies餐馆经营数据汇总
// @namespace    http://tampermonkey.net/
// @version      v1.35
// @description  页面内嵌于餐馆备货提醒上方，每 6 小时自动全量读取一轮（每家餐馆间隔 10 秒），自动适配游戏暗色/浅色主题
// @author       风月酱
// @match        *://www.simcompanies.com/*
// @grant        unsafeWindow
// @run-at       document-start
// ==/UserScript==

(function () {
    'use strict';

    const W = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
    const INSTALL_KEY = '__SC_RESTAURANT_STATS_V71_INSTALLED__';
    const STORAGE_KEY = 'sc_restaurants_global_data_v4';
    const REQUEST_TIME_KEY = 'sc_restaurant_stats_v7_last_api_request';
    const BUILDINGS_URL = '/api/v2/companies/me/buildings/';
    const RUNS_URL_PREFIX = '/api/v2/companies/buildings/';
    const HOST_ID = 'sc-restaurant-stats-host-v7';

    const MIN_REQUEST_INTERVAL_MS = 10 * 1000;
    const CYCLE_INTERVAL_MS = 6 * 60 * 60 * 1000;
    const RUNS_CACHE_TTL_MS = CYCLE_INTERVAL_MS;
    const DOM_FRESH_TTL_MS = 60 * 60 * 1000;
    const FAILED_RETRY_TTL_MS = 2 * 60 * 60 * 1000;
    const QUEUE_STATE_KEY = 'sc_restaurant_stats_v7_queue_state';
    const PAUSE_KEY = 'sc_restaurant_stats_v7_paused';
    const LAST_CYCLE_START_KEY = 'sc_restaurant_stats_v7_last_cycle_start';
    const LAST_CYCLE_DONE_KEY = 'sc_restaurant_stats_v7_last_cycle_done';
    const BUILDINGS_RETRY_DELAYS = [30 * 1000, 60 * 1000, 120 * 1000];

    try {
        if (W[INSTALL_KEY]) return;
        W[INSTALL_KEY] = true;
    } catch (_) {}

    let restaurants = {};
    let buildings = [];
    let rawRuns = {};
    let queueIds = [];
    let queueRunning = false;
    let queuePaused = false;
    let queueForce = false;
    let queueDone = 0;
    let queueTotal = 0;
    let queueWaitUntil = 0;
    let lastFetchError = '';
    let lastUrl = location.href;
    let ui = null;
    let domObserver = null;
    let themeObserver = null;
    let observedThemeBody = null;
    let colorSchemeQuery = null;
    let pageRefreshTimer = null;
    let watchdogTimer = null;
    let booted = false;
    let reminderAnchor = null;
    let buildingsRetryTimer = null;

    const log = (...args) => console.log('[餐馆收益统计 v7]', ...args);
    const warn = (...args) => console.warn('[餐馆收益统计 v7]', ...args);
    const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

    // -------------------- 数据存储 --------------------
    function loadData() {
        try {
            const parsed = JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}');
            restaurants = parsed && typeof parsed === 'object' && !Array.isArray(parsed) ? parsed : {};
        } catch (error) {
            restaurants = {};
            warn('本地餐馆缓存解析失败：', error);
        }
    }

    function saveData() {
        try {
            localStorage.setItem(STORAGE_KEY, JSON.stringify(restaurants));
        } catch (error) {
            warn('保存餐馆缓存失败：', error);
        }
    }

    function isRestaurant(building) {
        if (!building || typeof building !== 'object') return false;
        const kind = String(building.kind || '').toLowerCase();
        return kind === 'r' || kind === 'restaurant' ||
            Boolean(building.restaurantProperties) || Boolean(building.restaurantMenu);
    }

    function toMs(value) {
        if (value === null || value === undefined || value === '') return 0;
        if (typeof value === 'string' && !/^\d+(\.\d+)?$/.test(value.trim())) {
            const parsed = Date.parse(value);
            return Number.isFinite(parsed) ? parsed : 0;
        }
        const n = Number(value);
        if (!Number.isFinite(n) || n <= 0) return 0;
        return n < 1e12 ? n * 1000 : n;
    }

    function detectUpgrading(building) {
        if (!building || typeof building !== 'object') return false;
        if (building.upgrading === true || building.isUpgrading === true ||
            building.upgradeInProgress === true || building.underConstruction === true) return true;

        const now = Date.now();
        const upgrade = building.upgrade || building.upgradeInfo || building.restaurantProperties?.upgrade;
        if (upgrade && typeof upgrade === 'object') {
            const finish = toMs(upgrade.finishesAt || upgrade.completedAt || upgrade.endsAt || upgrade.finishAt);
            if (finish > now) return true;
            const start = toMs(upgrade.startedAt || upgrade.started);
            if (start > 0 && !finish) return true;
        }

        const finishFlat = toMs(building.upgradeFinishesAt || building.upgradeCompletedAt ||
            building.upgradeEndsAt || building.constructionCompletedAt);
        if (finishFlat > now) return true;
        const startFlat = toMs(building.upgradeStartedAt || building.constructionStartedAt);
        if (startFlat > 0 && !finishFlat) return true;

        const state = String(building.state || building.status || '').toLowerCase();
        return state === 'upgrading' || state === 'under_construction' || state === 'construction';
    }

    function extractList(data, ...keys) {
        if (Array.isArray(data)) return data;
        for (const key of keys) if (Array.isArray(data?.[key])) return data[key];
        return null;
    }
    const extractBuildingList = data => extractList(data, 'items', 'buildings');
    const extractRunList = data => extractList(data, 'runs', 'items', 'results');

    function toPercent(value) {
        const number = Number(value);
        if (!Number.isFinite(number)) return null;
        return number > 1 ? number : number * 100;
    }

    function toNumber(value) {
        if (value === null || value === undefined || value === '') return null;
        const number = Number(value);
        return Number.isFinite(number) ? number : null;
    }

    function applyBuilding(building) {
        if (!isRestaurant(building) || building.id === undefined || building.id === null) return false;
        const id = String(building.id);
        if (!restaurants[id]) restaurants[id] = { id };
        const item = restaurants[id];
        const props = building.restaurantProperties || {};

        item.id = id;
        item.name = String(building.name || building.customName || props.name || item.name || `餐馆 ${id}`);
        item.kind = building.kind || 'r';

        const price = props.menuPrice ?? building.menuPrice ?? building.price ??
            (Array.isArray(building.restaurantMenu) ? building.restaurantMenu[0]?.price : null);
        const rating = props.rating ?? building.rating;
        const occupancy = props.occupancy ?? building.occupancy;

        if (price !== undefined && price !== null) item.price = toNumber(price);
        if (rating !== undefined && rating !== null) item.ratingCurrent = toNumber(rating);
        if (occupancy !== undefined && occupancy !== null) {
            const percent = toPercent(occupancy);
            if (percent !== null) item.occupancy = percent;
        }

        const upgrading = detectUpgrading(building);
        if (item.upgrading && !upgrading) {
            item.runsFetchedAt = 0;
            item.runsError = '';
        }
        item.upgrading = upgrading;

        item.buildingUpdatedAt = Date.now();
        return true;
    }

    function processBuildings(data, source = '建筑列表') {
        const list = extractBuildingList(data);
        if (!list) {
            lastFetchError = `${source} 返回格式无法识别（不是数组）`;
            updateStatus();
            return false;
        }
        buildings = list;
        if (source.includes('页面')) {
            try { localStorage.setItem(REQUEST_TIME_KEY, String(Date.now())); } catch (_) {}
        }
        const restaurantBuildings = list.filter(isRestaurant);
        const liveIds = new Set(restaurantBuildings.map(b => String(b.id)));
        let changed = false;

        for (const oldId of Object.keys(restaurants)) {
            if (!liveIds.has(String(oldId))) {
                delete restaurants[oldId];
                changed = true;
            }
        }
        for (const building of restaurantBuildings) {
            if (applyBuilding(building)) changed = true;
        }

        // 跨天兜底：如果所有活跃餐馆都过期，说明是新一轮全量，忽略旧断点残留
        const activeItems = Object.values(restaurants).filter(item =>
            item && item.id !== undefined && !item.upgrading && liveIds.has(String(item.id)));
        if (activeItems.length > 0 && activeItems.every(item => !isRunCurrent(item))) {
            const saved = readQueueState();
            if (saved && saved.ids && saved.ids.length && activeItems.every(item => !runIsFresh(item, false))) {
                log('所有餐馆数据都已过期，忽略过期断点，从头开始新的一轮');
                clearQueueState();
            }
        }

        lastFetchError = '';
        if (changed) saveData();
        renderTable();
        updateStatus();
        const upgradingCount = restaurantBuildings.filter(detectUpgrading).length;
        log(`${source}：共 ${list.length} 座建筑，识别到 ${restaurantBuildings.length} 家餐馆（${upgradingCount} 家升级中跳过）`);

        if (!queueRunning && !queuePaused && restaurantBuildings.length) {
            setTimeout(() => startRunsQueue(false), 300);
        }
        return true;
    }

    function profitFromRun(run) {
        if (!run || typeof run !== 'object') return null;
        const direct = toNumber(run.profit);
        if (direct !== null) return direct;
        const revenue = toNumber(run.revenue);
        if (revenue === null) return null;
        return revenue - (toNumber(run.cogs) || 0) - (toNumber(run.wages) || 0);
    }

    function estimateNextCycle(sortedRuns) {
        const times = (sortedRuns || [])
            .map(run => Date.parse(run?.datetime || ''))
            .filter(time => Number.isFinite(time) && time > 0);
        if (times.length < 2) return 0;
        const gaps = [];
        for (let i = 1; i < Math.min(times.length, 6); i++) {
            const gap = times[i - 1] - times[i];
            if (gap > 2 * 3600 * 1000 && gap < 48 * 3600 * 1000) gaps.push(gap);
        }
        if (!gaps.length) return 0;
        gaps.sort((a, b) => a - b);
        const interval = gaps[Math.floor(gaps.length / 2)];
        let next = times[0] + interval;
        while (next <= Date.now()) next += interval;
        return next;
    }

    const sortRunsNewestFirst = list => list.slice().sort((a, b) =>
        (Date.parse(b?.datetime || '') || 0) - (Date.parse(a?.datetime || '') || 0));

    function processRestaurantRuns(id, data, source = '营业记录') {
        const list = extractRunList(data);
        const key = String(id);
        const item = restaurants[key];
        if (!item) {
            warn(`收到餐馆 ${key} 的营业记录，但建筑列表中尚未找到该餐馆`);
            return false;
        }
        if (!list) {
            item.runsError = `${source} 返回格式无法识别`;
            saveData();
            renderTable();
            updateStatus();
            return false;
        }

        rawRuns[key] = list;
        if (source.includes('页面')) {
            try { localStorage.setItem(REQUEST_TIME_KEY, String(Date.now())); } catch (_) {}
        }

        const sorted = sortRunsNewestFirst(list);
        const latestResolved = sorted.find(run => run && run.resolved !== false && profitFromRun(run) !== null);
        const latestAny = sorted[0] || null;
        const profitRun = latestResolved || (profitFromRun(latestAny) !== null ? latestAny : null);
        const ratingRun = sorted.find(run => run && (run.newRating != null || run.rating != null)) || latestAny;
        const occupancyRun = sorted.find(run => run && run.occupancy != null) || latestAny;

        if (profitRun) {
            const profit = profitFromRun(profitRun);
            if (profit !== null) item.profit = profit;
            item.profitDate = profitRun.datetime || null;
            item.profitResolved = profitRun.resolved !== false;
        }

        if (ratingRun) {
            const oldRating = toNumber(ratingRun.rating);
            const newRating = toNumber(ratingRun.newRating);
            if (oldRating !== null && newRating !== null) {
                item.ratingPrev = oldRating;
                item.ratingDiff = newRating - oldRating;
                if (item.ratingCurrent == null) item.ratingCurrent = newRating;
            } else if (newRating !== null && item.ratingCurrent == null) {
                item.ratingCurrent = newRating;
            }
        }

        if (occupancyRun && occupancyRun.occupancy != null) {
            const percent = toPercent(occupancyRun.occupancy);
            if (percent !== null) item.occupancy = percent;
        }
        if (latestAny && item.price == null && latestAny.menuPrice != null) {
            item.price = toNumber(latestAny.menuPrice);
        }

        const estimatedCycle = estimateNextCycle(sorted);
        if (estimatedCycle) item.cycleEstimateAt = estimatedCycle;

        item.runCount = list.length;
        item.runsFetchedAt = Date.now();
        item.runsFromDom = false;
        item.runsError = '';
        item.latestRunAt = latestAny?.datetime || null;
        saveData();
        renderTable();
        updateStatus();
        log(`餐馆 ${key} 营业记录读取完成（${list.length} 条，来源：${source}）`);
        return true;
    }

    // -------------------- API URL 识别与网络监听 --------------------
    function toUrl(input) {
        try {
            if (typeof input === 'string') return new URL(input, location.href);
            if (input && typeof input.url === 'string') return new URL(input.url, location.href);
            if (input && typeof input.href === 'string') return new URL(input.href, location.href);
        } catch (_) {}
        return null;
    }

    function isBuildingsUrl(input) {
        const url = toUrl(input);
        return Boolean(url && url.origin === location.origin &&
            url.pathname.replace(/\/$/, '') === BUILDINGS_URL.replace(/\/$/, ''));
    }

    function getRestaurantRunsId(input) {
        const url = toUrl(input);
        if (!url || url.origin !== location.origin) return null;
        const match = url.pathname.match(/^\/api\/v2\/companies\/buildings\/(\d+)\/restaurant-runs\/?$/);
        return match ? match[1] : null;
    }

    function installNetworkHooks() {
        try {
            const originalFetch = W.fetch;
            if (typeof originalFetch === 'function' && !originalFetch.__scRestaurantStatsV7) {
                const wrappedFetch = async function (...args) {
                    const response = await originalFetch.apply(this, args);
                    try {
                        if (response?.ok && isBuildingsUrl(args[0])) {
                            response.clone().json().then(data => processBuildings(data, '页面 fetch 拦截'))
                                .catch(error => warn('建筑列表 JSON 解析失败：', error));
                        } else {
                            const id = getRestaurantRunsId(args[0]);
                            if (id && response?.ok) {
                                response.clone().json().then(data => processRestaurantRuns(id, data, '页面 fetch 拦截'))
                                    .catch(error => warn(`餐馆 ${id} 营业记录 JSON 解析失败：`, error));
                            }
                        }
                    } catch (error) {
                        warn('Fetch 数据监听异常：', error);
                    }
                    return response;
                };
                wrappedFetch.__scRestaurantStatsV7 = true;
                W.fetch = wrappedFetch;
            }
        } catch (error) {
            warn('Fetch 监听安装失败：', error);
        }

        try {
            const proto = W.XMLHttpRequest && W.XMLHttpRequest.prototype;
            if (proto && !proto.open.__scRestaurantStatsV7) {
                const originalOpen = proto.open;
                const wrappedOpen = function (method, url, ...rest) {
                    const buildingRequest = isBuildingsUrl(url);
                    const restaurantId = getRestaurantRunsId(url);
                    if (buildingRequest || restaurantId) {
                        this.addEventListener('load', () => {
                            try {
                                if (this.status < 200 || this.status >= 300) return;
                                let data;
                                if (this.responseType === 'json') data = this.response;
                                else if (!this.responseType || this.responseType === 'text') data = JSON.parse(this.responseText);
                                if (buildingRequest) processBuildings(data, '页面 XHR 拦截');
                                else if (restaurantId) processRestaurantRuns(restaurantId, data, '页面 XHR 拦截');
                            } catch (error) {
                                warn('XHR 数据解析失败：', error);
                            }
                        }, { once: true });
                    }
                    return originalOpen.call(this, method, url, ...rest);
                };
                wrappedOpen.__scRestaurantStatsV7 = true;
                proto.open = wrappedOpen;
            }
        } catch (error) {
            warn('XHR 监听安装失败：', error);
        }
    }

    // -------------------- 受间隔限制的顺序请求 --------------------
    const lastOwnRequestAt = () => Number(localStorage.getItem(REQUEST_TIME_KEY) || 0) || 0;

    async function waitForRequestSlot() {
        while (true) {
            const remaining = Math.max(0, MIN_REQUEST_INTERVAL_MS - (Date.now() - lastOwnRequestAt()));
            queueWaitUntil = remaining ? Date.now() + remaining : 0;
            updateStatus();
            if (!remaining) return;
            await sleep(Math.min(remaining, 5000));
        }
    }

    async function limitedGetJson(path, respectPause = false) {
        await waitForRequestSlot();
        if (respectPause && queuePaused) {
            const paused = new Error('PAUSED');
            paused.paused = true;
            throw paused;
        }
        localStorage.setItem(REQUEST_TIME_KEY, String(Date.now()));
        const fetchFn = W.fetch || window.fetch;
        const response = await fetchFn.call(W, path, {
            method: 'GET',
            credentials: 'include',
            headers: { Accept: 'application/json' }
        });
        if (!response.ok) throw new Error(`HTTP ${response.status} ${response.statusText || ''}`.trim());
        return await response.json();
    }

    // 带自动重试：失败后按 30s / 60s / 120s 重试，避免"网络波动导致后续所有流程卡死"
    async function fetchBuildings(force = false, attempt = 0) {
        if (buildings.length && !force && attempt === 0) {
            startRunsQueue(false);
            return true;
        }
        try {
            lastFetchError = '';
            updateStatus();
            log(`开始读取完整建筑列表${attempt > 0 ? `（第 ${attempt + 1} 次尝试）` : ''}`);
            const data = await limitedGetJson(BUILDINGS_URL);
            if (buildingsRetryTimer) { clearTimeout(buildingsRetryTimer); buildingsRetryTimer = null; }
            return processBuildings(data, '主动建筑列表读取');
        } catch (error) {
            lastFetchError = error?.message || String(error);
            warn(`读取完整建筑列表失败（第 ${attempt + 1} 次）：`, error);
            updateStatus();
            if (attempt < BUILDINGS_RETRY_DELAYS.length && !queuePaused) {
                const delay = BUILDINGS_RETRY_DELAYS[attempt];
                log(`将在 ${formatDuration(delay)} 后自动重试读取建筑列表`);
                if (buildingsRetryTimer) clearTimeout(buildingsRetryTimer);
                buildingsRetryTimer = setTimeout(() => {
                    buildingsRetryTimer = null;
                    fetchBuildings(force, attempt + 1);
                }, delay);
            }
            return false;
        }
    }

    function isRunCurrent(item) {
        const fetchedAt = Number(item?.runsFetchedAt) || 0;
        return fetchedAt > 0 && Date.now() - fetchedAt < (item?.runsFromDom ? DOM_FRESH_TTL_MS : RUNS_CACHE_TTL_MS);
    }

    function runIsFresh(item, force) {
        if (force) return false;
        if (isRunCurrent(item)) return true;
        const failedAt = Number(item?.runsFailedAt) || 0;
        return failedAt > 0 && Date.now() - failedAt < FAILED_RETRY_TTL_MS;
    }

    // -------------------- 队列断点与 6 小时周期 --------------------
    function readQueueState() {
        try {
            const parsed = JSON.parse(localStorage.getItem(QUEUE_STATE_KEY) || 'null');
            if (parsed && Array.isArray(parsed.ids)) return parsed;
        } catch (_) {}
        return null;
    }

    function saveQueueState() {
        try {
            localStorage.setItem(QUEUE_STATE_KEY, JSON.stringify({
                ids: queueIds.slice(), done: queueDone, total: queueTotal, force: queueForce, at: Date.now()
            }));
        } catch (_) {}
    }

    function clearQueueState() {
        try { localStorage.removeItem(QUEUE_STATE_KEY); } catch (_) {}
    }

    const markCycleStart = () => { try { localStorage.setItem(LAST_CYCLE_START_KEY, String(Date.now())); } catch (_) {} };
    const markCycleDone = () => { try { localStorage.setItem(LAST_CYCLE_DONE_KEY, String(Date.now())); } catch (_) {} };

    function cycleBaseAt() {
        const doneAt = Number(localStorage.getItem(LAST_CYCLE_DONE_KEY) || 0) || 0;
        const startAt = Number(localStorage.getItem(LAST_CYCLE_START_KEY) || 0) || 0;
        return Math.max(doneAt, startAt);
    }

    function nextCycleAt() {
        const base = cycleBaseAt();
        return base ? base + CYCLE_INTERVAL_MS : 0;
    }

    function hasStaleRestaurant() {
        const liveIds = new Set(buildings.filter(isRestaurant).map(b => String(b.id)));
        return Object.values(restaurants).some(item =>
            item && item.id !== undefined && !item.upgrading &&
            liveIds.has(String(item.id)) && !runIsFresh(item, false));
    }

    function loadPauseState() {
        try { queuePaused = localStorage.getItem(PAUSE_KEY) === '1'; } catch (_) { queuePaused = false; }
    }

    function setPaused(paused) {
        queuePaused = Boolean(paused);
        try { localStorage.setItem(PAUSE_KEY, queuePaused ? '1' : '0'); } catch (_) {}
        log(queuePaused ? (queueRunning ? '已暂停读取，当前请求结束后队列停止' : '已暂停读取') : '已恢复读取');
        if (ui) {
            ui.pause.textContent = queuePaused ? '继续读取' : '暂停读取';
            if (!queuePaused && !queueRunning && buildings.length) startRunsQueue(false);
        }
        renderTable();
        updateStatus();
    }

    function startRunsQueue(force = false) {
        if (queuePaused) { updateStatus(); return; }
        if (queueRunning) return;
        const liveIds = new Set(buildings.filter(isRestaurant).map(b => String(b.id)));
        const eligible = id => liveIds.has(id) && !restaurants[id]?.upgrading;

        if (!force) {
            const saved = readQueueState();
            if (saved && saved.ids.length) {
                const resumed = saved.ids
                    .map(String)
                    .filter(id => eligible(id) && !runIsFresh(restaurants[id], false));
                if (resumed.length) {
                    queueIds = resumed;
                    // 断点只续跑剩余项，进度以"本次 resumed"为基准
                    queueDone = 0;
                    queueTotal = resumed.length;
                    queueForce = false;
                    queueWaitUntil = 0;
                    queueRunning = true;
                    updateStatus();
                    renderTable();
                    log(`从断点继续：本轮还剩 ${resumed.length} 家餐馆`);
                    processNextRun();
                    return;
                }
                clearQueueState();
            }
        }

        const ids = Object.values(restaurants)
            .filter(item => item && item.id !== undefined && !item.upgrading &&
                liveIds.has(String(item.id)) && !runIsFresh(item, force))
            .map(item => String(item.id));

        queueIds = ids;
        queueDone = 0;
        queueTotal = ids.length;
        queueForce = force;

        if (!ids.length) {
            updateStatus();
            log('没有需要读取的餐馆（其余在 6 小时有效期内或升级中）');
            return;
        }
        if (!force) markCycleStart();
        queueRunning = true;
        saveQueueState();
        updateStatus();
        log(`开始顺序补齐 ${ids.length} 家餐馆的营业记录（每家间隔 ${formatDuration(MIN_REQUEST_INTERVAL_MS)}）`);
        processNextRun();
    }

    async function processNextRun() {
        while (queueRunning && !queuePaused && queueIds.length) {
            const id = queueIds.shift();
            const item = restaurants[id];
            if (!item) { queueDone++; continue; }
            if (item.upgrading || runIsFresh(item, queueForce)) {
                queueDone++;
                saveQueueState();
                continue;
            }
            try {
                const path = `${RUNS_URL_PREFIX}${encodeURIComponent(id)}/restaurant-runs/`;
                log(`准备读取餐馆 ${id} 的营业记录`);
                const data = await limitedGetJson(path, true);
                processRestaurantRuns(id, data, '批量补齐');
            } catch (error) {
                if (error && error.paused) { queueIds.unshift(id); break; }
                item.runsError = error?.message || String(error);
                item.runsFailedAt = Date.now();
                saveData();
                warn(`餐馆 ${id} 营业记录读取失败：`, error);
            }
            queueDone++;
            saveQueueState();
            renderTable();
            updateStatus();
        }

        queueRunning = false;
        queueWaitUntil = 0;
        if (queuePaused) {
            saveQueueState();
            renderTable();
            updateStatus();
            log(`已暂停，本轮进度已保存（还剩 ${queueIds.length} 家）`);
            return;
        }
        clearQueueState();
        if (!queueForce && queueTotal && queueDone >= queueTotal) markCycleDone();
        renderTable();
        updateStatus();
        log('全餐馆营业记录队列处理完毕');
    }

    // -------------------- 面板定位（唯一锚点：餐馆备货提醒） --------------------
    function findReminderBlock() {
        if (reminderAnchor && reminderAnchor.isConnected) return reminderAnchor;
        if (!document.body) return null;
        const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, null, false);
        let node, guard = 0;
        while ((node = walker.nextNode()) && guard++ < 20000) {
            const text = String(node.nodeValue || '').replace(/\s+/g, ' ').trim();
            if (!text.includes('餐馆备货提醒')) continue;
            const element = node.parentElement;
            if (!element || element.closest('#' + HOST_ID)) continue;
            let block = element;
            for (let i = 0; i < 8 && block && block !== document.body; i++) {
                let rect = null;
                try { rect = block.getBoundingClientRect(); } catch (_) {}
                if (rect && rect.height >= 90) { reminderAnchor = block; return block; }
                block = block.parentElement;
            }
            reminderAnchor = element;
            return element;
        }
        return null;
    }

    // -------------------- 页面主题检测 --------------------
    function themeHintFromText(value) {
        const text = String(value || '').toLowerCase();
        if (!text) return null;
        if (/(^|[\s_-])(dark|night|black)([\s_-]|$)/.test(text)) return 'dark';
        if (/(^|[\s_-])(light|day|white)([\s_-]|$)/.test(text)) return 'light';
        return null;
    }

    function backgroundLuminance(element) {
        if (!element) return null;
        let color = '';
        try { color = getComputedStyle(element).backgroundColor || ''; } catch (_) { return null; }
        const match = color.match(/rgba?\(\s*([\d.]+)[, ]+\s*([\d.]+)[, ]+\s*([\d.]+)(?:\s*[,/]\s*([\d.]+%?))?/i);
        if (!match) return null;
        const alphaRaw = match[4];
        const alpha = alphaRaw === undefined ? 1 : (String(alphaRaw).includes('%') ? parseFloat(alphaRaw) / 100 : parseFloat(alphaRaw));
        if (!Number.isFinite(alpha) || alpha < 0.15) return null;
        const rgb = [Number(match[1]), Number(match[2]), Number(match[3])].map(v => Math.max(0, Math.min(255, v)) / 255);
        const linear = rgb.map(v => v <= 0.04045 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4));
        return 0.2126 * linear[0] + 0.7152 * linear[1] + 0.0722 * linear[2];
    }

    function detectPageTheme() {
        for (const el of [document.documentElement, document.body]) {
            if (!el) continue;
            const explicit = el.getAttribute('data-theme') ||
                el.getAttribute('data-bs-theme') ||
                el.getAttribute('data-color-scheme') ||
                el.getAttribute('theme');
            const hint = themeHintFromText(explicit) || themeHintFromText(el.className);
            if (hint) return hint;
        }
        const selectors = ['#root', '#app', 'main', '[id*="app"]', '[class*="app-container"]'];
        const nodes = [...document.querySelectorAll(selectors.join(',')), document.body, document.documentElement];
        for (const el of nodes) {
            const luminance = backgroundLuminance(el);
            if (luminance !== null) return luminance < 0.42 ? 'dark' : 'light';
        }
        try { if (colorSchemeQuery?.matches) return 'dark'; } catch (_) {}
        return 'light';
    }

    function updateTheme() {
        if (!ui?.host) return;
        const theme = detectPageTheme();
        if (ui.host.dataset.theme !== theme) {
            ui.host.dataset.theme = theme;
            ui.host.style.colorScheme = theme;
            log(`已切换为${theme === 'dark' ? '暗色' : '浅色'}主题`);
        }
    }

    function attachBodyThemeObserver() {
        if (!themeObserver || !document.body || observedThemeBody === document.body) return;
        observedThemeBody = document.body;
        themeObserver.observe(document.body, {
            attributes: true,
            attributeFilter: ['class', 'style', 'data-theme', 'data-bs-theme', 'data-color-scheme', 'theme']
        });
        updateTheme();
    }

    function installThemeWatchers() {
        updateTheme();
        if (themeObserver) themeObserver.disconnect();
        observedThemeBody = null;
        themeObserver = new MutationObserver(() => updateTheme());
        const options = { attributes: true, attributeFilter: ['class', 'style', 'data-theme', 'data-bs-theme', 'data-color-scheme', 'theme'] };
        if (document.documentElement) themeObserver.observe(document.documentElement, options);
        attachBodyThemeObserver();
        try {
            colorSchemeQuery = window.matchMedia('(prefers-color-scheme: dark)');
            colorSchemeQuery.addEventListener?.('change', updateTheme);
            if (!colorSchemeQuery.addEventListener) colorSchemeQuery.addListener?.(updateTheme);
        } catch (_) {}
    }

    // -------------------- 面板挂载 --------------------
    const HOST_STYLE = [
        'all: initial', 'display: block', 'position: static', 'float: none', 'clear: both',
        'width: 100%', 'max-width: 100%', 'grid-column: 1 / -1', 'flex-basis: 100%',
        'align-self: stretch', 'box-sizing: border-box',
        'margin: 6px 0 6px 0', 'padding: 6px 0 6px 0',
        'border-top: 1px dashed rgba(160,160,160,.55)',
        'border-bottom: 1px dashed rgba(160,160,160,.55)',
        'z-index: auto', 'pointer-events: auto'
    ].join(';');

    function placeHost() {
        if (!ui?.host) return false;
        const reminder = findReminderBlock();
        if (!reminder || !reminder.parentNode) return false;
        const host = ui.host;
        host.style.cssText = HOST_STYLE;
        if (host.nextSibling !== reminder || host.parentNode !== reminder.parentNode) {
            reminder.parentNode.insertBefore(host, reminder);
        }
        return true;
    }

    function ensureUI() {
        if (ui?.host) { placeHost(); return true; }
        if (!document.documentElement) return false;

        const oldHost = document.getElementById(HOST_ID);
        if (oldHost) oldHost.remove();

        const host = document.createElement('div');
        host.id = HOST_ID;
        const shadow = host.attachShadow ? host.attachShadow({ mode: 'open' }) : host;
        shadow.innerHTML = `
            <style>
                :host {
                    all: initial; display:block; width:100%;
                    color-scheme: dark;
                    --sc-panel-bg:rgb(59,61,61);
                    --sc-panel-text:#f1f1f1;
                    --sc-header-bg:#000000;
                    --sc-header-text:#ffffff;
                    --sc-status-bg:#1f2225;
                    --sc-status-text:rgba(255,255,255,.82);
                    --sc-table-head-bg:#26292c;
                    --sc-table-head-text:#ffffff;
                    --sc-border:rgba(255,255,255,.16);
                    --sc-row-hover:rgba(255,255,255,.09);
                    --sc-muted:rgba(255,255,255,.62);
                    --sc-button:rgba(255,255,255,.04);
                    --sc-button-muted:rgba(255,255,255,.04);
                    --sc-positive:#8fe0a9;
                    --sc-negative:#ff9999;
                    --sc-link:#7ec8ff;
                    --sc-link-hover:#a8dbff;
                    --sc-shadow:rgba(0,0,0,.20);
                }
                :host([data-theme="dark"]) {
                    color-scheme:dark;
                    --sc-panel-bg:rgb(59,61,61);
                    --sc-panel-text:#f1f1f1;
                    --sc-header-bg:#000000;
                    --sc-header-text:#ffffff;
                    --sc-status-bg:#1f2225;
                    --sc-status-text:rgba(255,255,255,.82);
                    --sc-table-head-bg:#26292c;
                    --sc-table-head-text:#ffffff;
                    --sc-border:rgba(255,255,255,.16);
                    --sc-row-hover:rgba(255,255,255,.09);
                    --sc-muted:rgba(255,255,255,.62);
                    --sc-button:rgba(255,255,255,.04);
                    --sc-button-muted:rgba(255,255,255,.04);
                    --sc-positive:#8fe0a9;
                    --sc-negative:#ff9999;
                    --sc-link:#7ec8ff;
                    --sc-link-hover:#a8dbff;
                    --sc-shadow:rgba(0,0,0,.20);
                }
                * { box-sizing:border-box; }
                .panel {
                    display:block; width:100%; max-height:min(64vh,650px); overflow:hidden;
                    color:var(--sc-panel-text); background:var(--sc-panel-bg);
                    border:1px solid var(--sc-border); border-radius:2px;
                    box-shadow:0 3px 12px var(--sc-shadow);
                    backdrop-filter:blur(3px); -webkit-backdrop-filter:blur(3px);
                    font:13px/1.4 Arial,"Microsoft YaHei",sans-serif;
                }
                .header { display:flex; align-items:center; justify-content:space-between; gap:10px;
                    padding:8px 10px; color:var(--sc-header-text); background:var(--sc-header-bg);
                    border-bottom:1px solid var(--sc-border); }
                .heading { color:var(--sc-header-text); font-size:14px; font-weight:700; white-space:nowrap; }
                .actions { display:flex; gap:5px; flex-wrap:wrap; justify-content:flex-end; }
                button { border:1px solid rgba(255,255,255,.68); border-radius:3px; padding:4px 8px;
                    color:#fff; background:var(--sc-button); cursor:pointer;
                    font:12px Arial,"Microsoft YaHei",sans-serif; }
                button:hover { background:rgba(255,255,255,.16); border-color:#fff; }
                button:disabled { opacity:.55; cursor:wait; }
                #debug,#hide,#queue,#pause { background:var(--sc-button-muted); }
                .status { padding:6px 10px; color:var(--sc-status-text); background:var(--sc-status-bg);
                    border-bottom:1px solid var(--sc-border); overflow-wrap:anywhere; font-size:12px; }
                .table-wrap { overflow:auto; max-height:min(46vh,470px); }
                table { width:100%; border-collapse:collapse; text-align:left; font-size:12px; color:var(--sc-panel-text); }
                th { position:sticky; top:0; z-index:1; background:var(--sc-table-head-bg);
                    color:var(--sc-table-head-text); font-weight:700; }
                th,td { padding:7px 9px; border-bottom:1px solid var(--sc-border); white-space:nowrap; }
                tbody tr:hover { background:var(--sc-row-hover); }
                td.name { max-width:190px; overflow:hidden; text-overflow:ellipsis; font-weight:600; }
                td.name a { color:var(--sc-link); text-decoration:none; cursor:pointer; }
                td.name a:hover { color:var(--sc-link-hover); text-decoration:underline; }
                td.profit { color:var(--sc-positive); font-weight:700; }
                td.state { font-size:11px; color:var(--sc-muted); }
                td.cycle { font-size:11px; color:var(--sc-muted); font-variant-numeric:tabular-nums; }
                td.cycle.started { color:#7ec8ff; }
                .state-loaded,.diff-positive { color:var(--sc-positive); }
                .state-error,.diff-negative { color:var(--sc-negative); }
                .state-pending,.diff-neutral { color:var(--sc-muted); }
                .state-skip { color:#ffcc80; }
                .empty { text-align:center; color:var(--sc-muted); padding:20px 10px; white-space:normal; }
                .minimized { display:none; }
                .reopen { display:inline-block; padding:6px 10px; border:1px solid rgba(255,255,255,.68);
                    border-radius:3px; color:#fff; background:rgba(43,46,49,.78); cursor:pointer; }
                @media(max-width:650px) { .header { align-items:flex-start; flex-direction:column; }
                    .heading { font-size:13px; } .table-wrap { max-height:42vh; } th,td { padding:6px 5px; } }
            </style>
            <section class="panel" id="panel">
                <div class="header">
                    <div class="heading">🍽️ 全餐馆经营数据汇总</div>
                    <div class="actions">
                        <button id="pause" type="button">暂停读取</button>
                        <button id="queue" type="button">刷新餐馆利润</button>
                        <button id="refresh" type="button">重新读取建筑</button>
                        <button id="debug" type="button">调试数据</button>
                        <button id="hide" type="button">收起</button>
                    </div>
                </div>
                <div class="status" id="status">统计面板已启动，正在读取建筑列表…</div>
                <div class="table-wrap">
                    <table>
                        <thead><tr>
                            <th>餐馆名字</th><th>利润</th><th>菜单价格</th><th>评分变化</th><th>上座率</th><th>周期开始</th><th>读取状态</th>
                        </tr></thead>
                        <tbody id="tbody"><tr><td class="empty" colspan="7">正在读取建筑列表…</td></tr></tbody>
                    </table>
                </div>
            </section>
            <div class="minimized" id="minimized"><span class="reopen" id="reopen">🍽️ 餐馆统计（展开）</span></div>
        `;

        ui = {
            host, shadow,
            panel: shadow.getElementById('panel'),
            status: shadow.getElementById('status'),
            tbody: shadow.getElementById('tbody'),
            pause: shadow.getElementById('pause'),
            queue: shadow.getElementById('queue'),
            refresh: shadow.getElementById('refresh'),
            debug: shadow.getElementById('debug'),
            hide: shadow.getElementById('hide'),
            minimized: shadow.getElementById('minimized'),
            reopen: shadow.getElementById('reopen')
        };

        ui.pause.addEventListener('click', () => setPaused(!queuePaused));
        ui.queue.addEventListener('click', () => { if (!queueRunning) startRunsQueue(true); });
        ui.refresh.addEventListener('click', async () => {
            if (queueRunning) return;
            ui.refresh.disabled = true;
            ui.refresh.textContent = '读取中…';
            try {
                if (buildings.length) {
                    for (const building of buildings.filter(isRestaurant)) applyBuilding(building);
                    saveData();
                    renderTable();
                    if (!queuePaused) startRunsQueue(false);
                } else {
                    await fetchBuildings(true);
                }
            } finally {
                ui.refresh.textContent = '重新读取建筑';
                ui.refresh.disabled = queueRunning;
                updateStatus();
            }
        });
        ui.debug.addEventListener('click', () => {
            alert(JSON.stringify({
                buildingsCount: buildings.length,
                restaurantCount: Object.keys(restaurants).length,
                queueRunning,
                queueRemaining: queueIds.length,
                sampleBuilding: buildings.find(isRestaurant) || buildings[0] || null,
                sampleRestaurant: Object.values(restaurants)[0] || null,
                sampleRuns: Object.keys(rawRuns).length ? rawRuns[Object.keys(rawRuns)[0]] : null,
                lastFetchError
            }, null, 2));
        });
        ui.hide.addEventListener('click', () => {
            ui.panel.style.display = 'none';
            ui.minimized.style.display = 'block';
        });
        ui.reopen.addEventListener('click', () => {
            ui.minimized.style.display = 'none';
            ui.panel.style.display = 'block';
        });

        placeHost();
        updateTheme();
        renderTable();
        updateStatus();
        log('界面已创建，正在定位到“餐馆备货提醒”上方');
        return true;
    }

    function escapeHtml(value) {
        return String(value ?? '').replace(/[&<>"']/g, char => ({
            '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
        })[char]);
    }

    // -------------------- 状态与表格渲染 --------------------
    function formatDuration(ms) {
        const totalSec = Math.max(0, Math.round(ms / 1000));
        const hours = Math.floor(totalSec / 3600);
        const mins = Math.floor((totalSec % 3600) / 60);
        const secs = totalSec % 60;
        if (hours > 0) return `${hours} 小时 ${mins} 分`;
        if (mins > 0) return `${mins} 分 ${secs} 秒`;
        return `${secs} 秒`;
    }

    function getRunState(item) {
        if (item.upgrading) return '升级中';
        const key = String(item.id);
        const index = queueRunning ? queueIds.indexOf(key) : -1;
        const total = queueTotal || queueIds.length;
        if (index === 0) {
            const wait = queueWaitUntil ? Math.max(0, queueWaitUntil - Date.now()) : 0;
            return wait > 0 ? `读取中 · ${formatDuration(wait)}` : '读取中';
        }
        if (index > 0) {
            const wait = (queueWaitUntil ? Math.max(0, queueWaitUntil - Date.now()) : 0)
                + (index - 1) * MIN_REQUEST_INTERVAL_MS;
            return `排队 ${index + 1}/${total} · ${formatDuration(wait)}`;
        }
        if (isRunCurrent(item)) return '已完成';
        if (item.runsError) return '失败';
        return '未完成';
    }

    const buildingUrl = id => `/b/${encodeURIComponent(id)}/`;

    function cycleStartOf(item) {
        const at = Number(item?.cycleAt) || Number(item?.cycleEstimateAt) || 0;
        if (!at) return { at: 0, text: '-', fromDom: false, started: false };
        const fromDom = Boolean(Number(item?.cycleAt));
        const now = Date.now();
        if (at <= now) return { at, text: '已开始', fromDom, started: true };

        const d = new Date(at);
        const pad = n => String(n).padStart(2, '0');
        const hm = `${pad(d.getHours())}:${pad(d.getMinutes())}`;
        const today = new Date();
        const tomorrow = new Date(now + 24 * 3600 * 1000);
        let label = hm;
        if (d.toDateString() === today.toDateString()) label = hm;
        else if (d.toDateString() === tomorrow.toDateString()) label = `明天 ${hm}`;
        else label = `${pad(d.getMonth() + 1)}-${pad(d.getDate())} ${hm}`;
        return { at, text: (fromDom ? '' : '~') + label, fromDom, started: false };
    }

    function renderTable() {
        if (!ui?.tbody) return;
        const sorted = Object.values(restaurants).sort((a, b) => {
            const na = parseInt(String(a.name || '').replace(/[^0-9]/g, ''), 10) || 0;
            const nb = parseInt(String(b.name || '').replace(/[^0-9]/g, ''), 10) || 0;
            return na - nb || Number(a.id) - Number(b.id);
        });

        if (!sorted.length) {
            ui.tbody.innerHTML = '<tr><td class="empty" colspan="7">尚未识别到餐馆。请等待建筑列表读取，或检查控制台错误。</td></tr>';
            return;
        }

        ui.tbody.innerHTML = sorted.map(item => {
            const safeName = escapeHtml(item.name || `餐馆 ${item.id}`);
            const nameHtml = `<a href="${buildingUrl(item.id)}" target="_blank" rel="noopener noreferrer" title="打开 ${safeName}">${safeName}</a>`;

            let rating = '-';
            if (item.ratingCurrent != null) {
                const diff = toNumber(item.ratingDiff);
                const diffClass = diff > 0 ? 'diff-positive' : diff < 0 ? 'diff-negative' : 'diff-neutral';
                const prev = item.ratingPrev != null ? `${Number(item.ratingPrev).toFixed(2)} ` : '';
                const diffHtml = diff !== null
                    ? `<span class="${diffClass}">(${diff > 0 ? '+' : ''}${diff.toFixed(2)})</span> ` : '';
                rating = `${prev}${diffHtml}${Number(item.ratingCurrent).toFixed(2)}`;
            }

            const profit = item.profit != null
                ? '$' + Number(item.profit).toLocaleString(undefined, { maximumFractionDigits: 2 }) : '-';
            const price = item.price != null ? '$' + escapeHtml(item.price) : '-';
            const occupancy = item.occupancy != null ? `${Number(item.occupancy).toFixed(2)}%` : '-';

            const cycle = item.upgrading
                ? { text: '升级中', started: false, fromDom: false, at: 0 }
                : cycleStartOf(item);
            const cycleClass = cycle.started ? 'cycle started' : 'cycle';
            const cycleTitle = item.upgrading
                ? '建筑升级中，无营业周期'
                : !cycle.at
                    ? '还没有周期数据'
                    : (cycle.fromDom ? '周期时间来自该餐馆页面' : '周期时间按营业记录推算');

            const state = getRunState(item);
            const stateClass = state.startsWith('升级中') ? 'state-skip'
                : state.startsWith('已完成') ? 'state-loaded'
                : state.startsWith('失败') ? 'state-error' : 'state-pending';
            const stateTitle = item.upgrading
                ? '建筑升级中，不营业，已跳过营业记录识别'
                : item.runsError
                    ? ` title="${escapeHtml(item.runsError)}"`
                    : (state.startsWith('已完成') && item.runsFetchedAt
                        ? ` title="读取于 ${escapeHtml(new Date(item.runsFetchedAt).toLocaleTimeString())}"`
                        : '');

            return `<tr>
                <td class="name" title="${safeName}">${nameHtml}</td>
                <td class="profit">${escapeHtml(profit)}</td>
                <td>${price}</td>
                <td>${rating}</td>
                <td>${escapeHtml(occupancy)}</td>
                <td class="${cycleClass}" title="${escapeHtml(cycleTitle)}">${escapeHtml(cycle.text)}</td>
                <td class="state ${stateClass}"${stateTitle}>${state}</td>
            </tr>`;
        }).join('');
    }

    function updateStatus() {
        if (!ui?.status) return;
        const all = Object.values(restaurants);
        const upgradingCount = all.filter(item => item.upgrading).length;
        const active = all.filter(item => !item.upgrading);
        const total = active.length;
        const done = active.filter(isRunCurrent).length;
        const failed = active.filter(item => !isRunCurrent(item) && item.runsError).length;
        const pending = Math.max(0, total - done - failed);
        const staleCount = active.filter(item => !isRunCurrent(item)).length;
        const cycleText = (!queueRunning && pending === 0 && failed === 0)
            ? '本轮读取已全部完成'
            : `本轮完成 ${done}/${total} 家${pending ? `，待补齐 ${pending} 家` : ''}${failed ? `，失败 ${failed} 家` : ''}`;
        const upgradeText = upgradingCount ? `（其中 ${upgradingCount} 家升级中，已跳过识别）` : '';
        const staleText = (!queueRunning && staleCount > 0) ? ` 有 ${staleCount} 家数据已过期，正在等待重新读取。` : '';
        let text = buildings.length
            ? `已读取 ${buildings.length} 座建筑，识别到 ${all.length} 家餐馆${upgradeText}；${cycleText}。${staleText}`
            : (lastFetchError
                ? `等待建筑列表读取（上次失败：${lastFetchError}），将自动重试…`
                : '面板已启动，等待完整建筑列表…');

        if (queueRunning) {
            const leftCount = Math.max(1, queueTotal - queueDone);
            const nextSlotMs = queueWaitUntil ? Math.max(0, queueWaitUntil - Date.now()) : 0;
            const leftMs = nextSlotMs + (leftCount - 1) * MIN_REQUEST_INTERVAL_MS;
            text += ` 当前队列 ${queueDone}/${queueTotal}；${formatDuration(leftMs)}（预计 ${new Date(Date.now() + leftMs).toLocaleTimeString()} 读完）。`;
        } else if (queueTotal && queueDone >= queueTotal) {
            text += ' 本轮队列已结束。';
        }
        if (lastFetchError && buildings.length) text += ` 错误：${lastFetchError}`;

        const nextReadAt = queueRunning ? 0 : nextCycleAt();
        if (nextReadAt) {
            const leftMs = nextReadAt - Date.now();
            if (leftMs > 0) {
                const leftHours = Math.floor(leftMs / 3600000);
                const leftMins = Math.floor((leftMs % 3600000) / 60000);
                text += ` 下次全量读取倒计时 ${leftHours} 小时 ${leftMins} 分（${new Date(nextReadAt).toLocaleTimeString()} 可再读）。`;
            } else {
                text += ' 可重新全量读取了，点“刷新餐馆利润”开始。';
            }
        }
        if (queuePaused) text += ' 已暂停读取，点“继续读取”恢复。';
        ui.status.textContent = text;

        if (ui.queue) ui.queue.disabled = queuePaused || queueRunning || !total;
        if (ui.pause) ui.pause.textContent = queuePaused ? '继续读取' : '暂停读取';
        if (ui.refresh) ui.refresh.disabled = queueRunning;
    }

    // -------------------- 当前打开餐馆页面 DOM 兜底 --------------------
    function getCurrentBuildingId() {
        const match = location.pathname.match(/\/(?:b|building|buildings)\/(\d+)(?:\/|$)/);
        return match ? String(match[1]) : null;
    }

    function parseCycle(text) {
        const flat = String(text || '').replace(/\s+/g, ' ');
        const patterns = [
            /(?:下一周期|下一个周期|下个周期)[^0-9]{0,10}([0-9]{1,2})[:：]([0-9]{2})[:：]([0-9]{2})/,
            /next cycle[^0-9]{0,20}([0-9]{1,2}):([0-9]{2}):([0-9]{2})/i
        ];
        for (const pattern of patterns) {
            const match = flat.match(pattern);
            if (!match || match.index === undefined) continue;
            const seconds = Number(match[1]) * 3600 + Number(match[2]) * 60 + Number(match[3]);
            const tail = flat.slice(match.index, match.index + match[0].length + 24);
            const clock = tail.match(/[（(]\s*([0-9]{1,2})[:：]([0-9]{2})\s*[)）]/);
            return {
                at: Date.now() + seconds * 1000,
                clock: clock ? `${String(clock[1]).padStart(2, '0')}:${clock[2]}` : '',
                leftText: `${match[1]}:${match[2]}:${match[3]}`
            };
        }
        return null;
    }

    function extractDomData() {
        if (!document.body) return null;
        const text = document.body.innerText || '';
        const title = document.querySelector('h1,h2,h3');
        const result = {
            profit: null, price: null,
            ratingPrev: null, ratingDiff: null, ratingCurrent: null,
            occupancy: null,
            domTitle: title?.textContent?.trim() || null,
            cycle: parseCycle(text)
        };
        const profitMatch = text.match(/利润[:：]\s*\$([0-9,]+(?:\.[0-9]+)?)/);
        if (profitMatch) result.profit = parseFloat(profitMatch[1].replace(/,/g, ''));
        const priceMatch = text.match(/\$([0-9,]+(?:\.[0-9]+)?)\s*菜单价格/);
        if (priceMatch) result.price = parseFloat(priceMatch[1].replace(/,/g, ''));
        const ratingMatch = text.match(/([0-9.]+)\s*\(([+-][0-9.]+)\)\s*([0-9.]+)/);
        if (ratingMatch) {
            result.ratingPrev = parseFloat(ratingMatch[1]);
            result.ratingDiff = parseFloat(ratingMatch[2]);
            result.ratingCurrent = parseFloat(ratingMatch[3]);
        }
        const occupancyMatch = text.match(/([0-9]+(?:\.[0-9]+)?)%\s*上座率/);
        if (occupancyMatch) result.occupancy = parseFloat(occupancyMatch[1]);
        return result;
    }

    function updateCurrentFromDom() {
        const id = getCurrentBuildingId();
        if (!id) return;
        const item = restaurants[id];
        if (item?.upgrading) return;
        const data = extractDomData();
        if (!data) return;
        if (!restaurants[id]) restaurants[id] = { id };
        const target = restaurants[id];
        let changed = false;

        if (data.cycle?.at &&
            (!target.cycleAt || Math.abs(Number(target.cycleAt) - data.cycle.at) > 60 * 1000)) {
            target.cycleAt = data.cycle.at;
            target.cycleClock = data.cycle.clock || '';
            changed = true;
        }
        if (data.domTitle && target.name !== data.domTitle) { target.name = data.domTitle; changed = true; }

        // 关键修复：只有利润真的变了 / 首次 / DOM 标记已超过 1 小时，才刷新时间戳。
        // 否则停留在旧餐馆页面会永远把 runsFetchedAt 刷成"现在"，导致该餐馆永不重新读取。
        if (data.profit !== null) {
            const profitChanged = target.profit !== data.profit;
            if (profitChanged) {
                target.profit = data.profit;
                changed = true;
            }
            const lastDomMark = Number(target.lastDomMarkAt) || 0;
            const domExpired = !lastDomMark || (Date.now() - lastDomMark) >= DOM_FRESH_TTL_MS;
            const neverFetched = !target.runsFetchedAt;
            if (profitChanged || neverFetched || domExpired) {
                target.runsFetchedAt = Date.now();
                target.runsFromDom = true;
                target.runsError = '';
                target.lastDomMarkAt = Date.now();
                changed = true;
            }
        }

        if (data.price !== null && target.price !== data.price) { target.price = data.price; changed = true; }
        if (data.ratingCurrent !== null &&
            (target.ratingCurrent !== data.ratingCurrent || target.ratingDiff !== data.ratingDiff)) {
            target.ratingPrev = data.ratingPrev;
            target.ratingDiff = data.ratingDiff;
            target.ratingCurrent = data.ratingCurrent;
            changed = true;
        }
        if (data.occupancy !== null && target.occupancy !== data.occupancy) { target.occupancy = data.occupancy; changed = true; }

        if (changed) { saveData(); renderTable(); updateStatus(); }
    }

    // -------------------- 启动与路由监听 --------------------
    let lastDomSyncAt = 0;

    function schedulePageRefresh() {
        if (pageRefreshTimer) clearTimeout(pageRefreshTimer);
        pageRefreshTimer = setTimeout(() => {
            if (document.hidden) return;
            attachBodyThemeObserver();
            if (!ui?.host) ensureUI();
            else placeHost();
            if (Date.now() - lastDomSyncAt < 2000) return;
            lastDomSyncAt = Date.now();
            updateTheme();
            updateCurrentFromDom();
        }, 250);
    }

    function boot() {
        if (booted) return;
        booted = true;
        loadData();
        loadPauseState();
        installNetworkHooks();
        try { ensureUI(); } catch (error) { warn('界面创建失败：', error); }
        installThemeWatchers();
        renderTable();
        updateStatus();

        // 启动诊断：明确打印当前缓存新鲜度，便于排查"跨天没刷新"的问题
        const now = Date.now();
        const allItems = Object.values(restaurants).filter(item => item && item.id !== undefined && !item.upgrading);
        const staleList = allItems.filter(item => !isRunCurrent(item));
        if (allItems.length) {
            log(`启动诊断：共 ${allItems.length} 家活跃餐馆，${staleList.length} 家数据已过期，${allItems.length - staleList.length} 家仍新鲜`);
            if (staleList.length) log(`过期餐馆：${staleList.map(i => `${i.name || i.id}(${Math.round((now - (Number(i.runsFetchedAt) || 0)) / 3600000)}h)`).join(', ')}`);
        }
        if (queuePaused) warn('本地暂停状态为"暂停"，如需读取请点"继续读取"');

        if (document.documentElement && !domObserver) {
            domObserver = new MutationObserver(() => schedulePageRefresh());
            domObserver.observe(document.documentElement, { childList: true, subtree: true, characterData: true });
        }

        updateCurrentFromDom();

        setTimeout(() => {
            if (queuePaused) return;
            if (!buildings.length) fetchBuildings();
            else startRunsQueue(false);
        }, 3000);

        if (watchdogTimer) clearInterval(watchdogTimer);
        watchdogTimer = setInterval(() => {
            if (!ui?.host || ui.host.isConnected) return;
            placeHost();
        }, 3000);

        setInterval(() => {
            if (queueRunning || queuePaused) return;
            // 建筑列表为空且没有正在进行的重试 -> 主动请求一次
            if (!buildings.length) {
                if (!buildingsRetryTimer) fetchBuildings();
                return;
            }
            if (hasStaleRestaurant()) startRunsQueue(false);
        }, 5 * 60 * 1000);

        setInterval(() => {
            if (lastUrl !== location.href) {
                lastUrl = location.href;
                reminderAnchor = null;
                if (ui?.host && ui.host.parentNode) ui.host.remove();
                lastDomSyncAt = 0;
                schedulePageRefresh();
            }
        }, 1000);

        setInterval(() => {
            if (document.hidden || !queueRunning) return;
            renderTable();
            updateStatus();
        }, 1000);

        setInterval(() => {
            if (document.hidden) return;
            if (ui?.tbody) renderTable();
            updateStatus();
        }, 60 * 1000);

        log('脚本启动完成。统计面板仅会以内嵌形式显示在“餐馆备货提醒”所在区块上方。');
    }

    if (document.documentElement) {
        boot();
    } else {
        const rootObserver = new MutationObserver(() => {
            if (document.documentElement) {
                rootObserver.disconnect();
                boot();
            }
        });
        rootObserver.observe(document, { childList: true, subtree: true });
        document.addEventListener('DOMContentLoaded', boot, { once: true });
    }
})();
//（注：内容由AI生成）