const os = require("node:os");
const LOGICAL_CPUS = Math.max(1, os.cpus().length);
const DEFAULT_UV_THREADPOOL_SIZE = Math.min(
  128,
  Math.max(32, LOGICAL_CPUS * 4)
);

if (!process.env.UV_THREADPOOL_SIZE) {
  process.env.UV_THREADPOOL_SIZE = String(DEFAULT_UV_THREADPOOL_SIZE);
}

const fs = require("node:fs");
const fsp = require("node:fs/promises");
const https = require("node:https");
const path = require("node:path");
const zlib = require("node:zlib");
const { pipeline } = require("node:stream/promises");
const {
  Worker,
  isMainThread,
  parentPort,
  workerData,
} = require("node:worker_threads");
const Rlog = require("rlog-js");

const DATA_ROOT = path.join(process.cwd(), "data");
const LEGACY_SOURCE_ROOT = path.join(DATA_ROOT, "sources");
const CACHE_ROOT = path.join(process.cwd(), "cache");

const CACHE_FILES = {
  countries: path.join(CACHE_ROOT, "countries-states-cities.json"),
  states: path.join(CACHE_ROOT, "states.json"),
  citiesGz: path.join(CACHE_ROOT, "cities.json.gz"),
  cities: path.join(CACHE_ROOT, "cities.json"),
};

const SOURCE_URLS = {
  countries:
    "https://raw.githubusercontent.com/dr5hn/countries-states-cities-database/refs/heads/master/json/countries%2Bstates%2Bcities.json",
  states:
    "https://github.com/dr5hn/countries-states-cities-database/raw/refs/heads/master/json/states.json",
  citiesGz:
    "https://github.com/dr5hn/countries-states-cities-database/raw/refs/heads/master/json/cities.json.gz",
};

const DEFAULT_WORKER_COUNT = LOGICAL_CPUS;
const DEFAULT_WRITE_CONCURRENCY = Math.min(
  1024,
  Math.max(256, LOGICAL_CPUS * 32)
);

const WINDOWS_RESERVED_NAMES = new Set([
  "CON",
  "PRN",
  "AUX",
  "NUL",
  "COM1",
  "COM2",
  "COM3",
  "COM4",
  "COM5",
  "COM6",
  "COM7",
  "COM8",
  "COM9",
  "LPT1",
  "LPT2",
  "LPT3",
  "LPT4",
  "LPT5",
  "LPT6",
  "LPT7",
  "LPT8",
  "LPT9",
]);

const rlog = new Rlog({
  timezone: "Asia/Shanghai",
});

function exists(filePath) {
  try {
    fs.accessSync(filePath, fs.constants.F_OK);
    return true;
  } catch {
    return false;
  }
}

async function ensureDirectory(dirPath) {
  await fsp.mkdir(dirPath, { recursive: true });
}

function formatMB(byteCount) {
  return (byteCount / (1024 * 1024)).toFixed(2);
}

function parsePositiveInt(value, fallback) {
  const parsed = Number(value);
  if (Number.isInteger(parsed) && parsed > 0) {
    return parsed;
  }
  return fallback;
}

function resolveWorkerCount(countryCount) {
  const requested = parsePositiveInt(
    process.env.GEN_WORKERS || process.env.WORKERS,
    DEFAULT_WORKER_COUNT
  );
  return Math.max(1, Math.min(requested, countryCount));
}

function resolveWriteConcurrency(workerCount) {
  const autoConcurrency = Math.min(4096, Math.max(DEFAULT_WRITE_CONCURRENCY, workerCount * 128));
  return parsePositiveInt(process.env.WRITE_CONCURRENCY, autoConcurrency);
}

function sanitizePathSegment(input, fallback) {
  const raw = String(input ?? "").trim();
  const withSafeChars = raw
    .replace(/[<>:"/\\|?*\u0000-\u001F]/g, "_")
    .replace(/[. ]+$/g, "");
  const candidate = withSafeChars || fallback;
  if (WINDOWS_RESERVED_NAMES.has(candidate.toUpperCase())) {
    return `${candidate}_`;
  }
  return candidate;
}

function writeJsonFile(filePath, data) {
  return fsp.writeFile(filePath, `${JSON.stringify(data, null, 2)}\n`, "utf8");
}

function getUniqueSorted(values) {
  return Array.from(new Set(values)).sort((a, b) =>
    String(a).localeCompare(String(b))
  );
}

function resolveLocalizedName(entity, language) {
  if (!entity || typeof entity !== "object") {
    return "";
  }

  const fallbackName = entity.name ?? "";
  const translations =
    entity.translations && typeof entity.translations === "object"
      ? entity.translations
      : null;

  if (!translations) {
    return fallbackName;
  }

  const normalizedLanguage = String(language || "").replace("_", "-");
  const lowerLanguage = normalizedLanguage.toLowerCase();
  const keys = [
    normalizedLanguage,
    lowerLanguage,
    normalizedLanguage.replace("-", "_"),
  ];

  if (lowerLanguage === "zh-cn") {
    keys.push("zh", "cn");
  }

  for (const key of keys) {
    if (translations[key]) {
      return translations[key];
    }
  }

  return fallbackName;
}

function normalizeLocaleKey(locale) {
  const raw = String(locale ?? "").trim();
  if (!raw) {
    return null;
  }

  const hyphenated = raw.replace(/_/g, "-");
  try {
    const normalized = Intl.getCanonicalLocales(hyphenated);
    if (normalized.length > 0) {
      return normalized[0];
    }
  } catch {
    return hyphenated;
  }

  return hyphenated;
}

function discoverLanguages(countries, stateById, cityById) {
  const countryLanguages = new Set();
  const stateLanguages = new Set();
  const cityLanguages = new Set();

  const addFromEntity = (entity, targetSet) => {
    const translations =
      entity && typeof entity === "object" && entity.translations
        ? entity.translations
        : null;
    if (!translations || typeof translations !== "object") {
      return;
    }
    for (const key of Object.keys(translations)) {
      const normalized = normalizeLocaleKey(key);
      if (normalized) {
        targetSet.add(normalized);
      }
    }
  };

  for (const country of countries) {
    addFromEntity(country, countryLanguages);
  }

  for (const state of stateById.values()) {
    addFromEntity(state, stateLanguages);
  }

  for (const city of cityById.values()) {
    addFromEntity(city, cityLanguages);
  }

  const union = new Set([...countryLanguages, ...stateLanguages, ...cityLanguages]);
  const core = Array.from(countryLanguages).filter(
    (locale) => stateLanguages.has(locale) && cityLanguages.has(locale)
  );

  return {
    countries: Array.from(countryLanguages).sort((a, b) => a.localeCompare(b)),
    states: Array.from(stateLanguages).sort((a, b) => a.localeCompare(b)),
    cities: Array.from(cityLanguages).sort((a, b) => a.localeCompare(b)),
    core: core.sort((a, b) => a.localeCompare(b)),
    union: Array.from(union).sort((a, b) => a.localeCompare(b)),
  };
}

function parseRequestedLanguages(discoveredLanguages) {
  const cliLocales = process.argv.find((arg) => arg.startsWith("--locales="));
  const envLocales = process.env.LOCALES;
  const rawInput = cliLocales
    ? cliLocales.slice("--locales=".length)
    : envLocales;

  if (!rawInput) {
    return discoveredLanguages;
  }

  const requested = rawInput
    .split(",")
    .map((item) => normalizeLocaleKey(item))
    .filter(Boolean);

  if (requested.length === 0) {
    return discoveredLanguages;
  }

  const discoveredSet = new Set(discoveredLanguages);
  const matched = requested.filter((locale) => discoveredSet.has(locale));
  const missing = requested.filter((locale) => !discoveredSet.has(locale));

  if (missing.length > 0) {
    rlog.warn(`Ignored unknown locales: ${missing.join(", ")}`);
  }

  if (matched.length === 0) {
    rlog.warn("No requested locales found in source data, using discovered locales");
    return discoveredLanguages;
  }

  return matched;
}

function parseDiscoveryMode() {
  const cliMode = process.argv.find((arg) =>
    arg.startsWith("--locale-discovery=")
  );
  const envMode = process.env.LOCALE_DISCOVERY;
  const rawMode = cliMode
    ? cliMode.slice("--locale-discovery=".length)
    : envMode;
  const mode = String(rawMode || "core").trim().toLowerCase();
  if (mode === "union") {
    return "union";
  }
  return "core";
}

function getStateCode(state) {
  if (state?.iso2 && String(state.iso2).trim()) {
    return String(state.iso2).trim();
  }

  const iso3166 = String(state?.iso3166_2 ?? "").trim();
  if (iso3166) {
    const parts = iso3166.split("-");
    const lastPart = parts[parts.length - 1];
    if (lastPart) {
      return lastPart;
    }
    return iso3166;
  }

  return sanitizePathSegment(state?.name, `state-${state?.id ?? "unknown"}`);
}

function buildCountryDetail(country, language) {
  return {
    id: country.id,
    code: country.iso2,
    iso3: country.iso3,
    numeric_code: country.numeric_code,
    name: resolveLocalizedName(country, language),
    name_default: country.name,
    native: country.native,
    capital: country.capital,
    phonecode: country.phonecode,
    currency: country.currency,
    currency_name: country.currency_name,
    currency_symbol: country.currency_symbol,
    tld: country.tld,
    population: country.population,
    gdp: country.gdp,
    region: country.region,
    region_id: country.region_id,
    subregion: country.subregion,
    subregion_id: country.subregion_id,
    nationality: country.nationality,
    timezones: Array.isArray(country.timezones) ? country.timezones : [],
    latitude: country.latitude,
    longitude: country.longitude,
    emoji: country.emoji,
    emojiU: country.emojiU,
  };
}

function buildStateDetail(baseState, translatedState, countryCode, language) {
  const source = translatedState || baseState;
  return {
    id: source.id ?? baseState.id,
    code: getStateCode(source),
    iso2: source.iso2 ?? baseState.iso2 ?? null,
    iso3166_2: source.iso3166_2 ?? baseState.iso3166_2 ?? null,
    fips_code: source.fips_code ?? null,
    name: resolveLocalizedName(source, language),
    name_default: source.name ?? baseState.name,
    native: source.native ?? baseState.native ?? null,
    type: source.type ?? baseState.type ?? null,
    level: source.level ?? null,
    parent_id: source.parent_id ?? null,
    population: source.population ?? null,
    latitude: source.latitude ?? baseState.latitude ?? null,
    longitude: source.longitude ?? baseState.longitude ?? null,
    timezone: source.timezone ?? baseState.timezone ?? null,
    wikiDataId: source.wikiDataId ?? null,
    country_code: countryCode,
  };
}

function buildCityDetail(
  baseCity,
  translatedCity,
  countryCode,
  stateCode,
  language
) {
  const source = translatedCity || baseCity;
  return {
    id: source.id ?? baseCity.id,
    name: resolveLocalizedName(source, language),
    name_default: source.name ?? baseCity.name,
    native: source.native ?? null,
    type: source.type ?? null,
    level: source.level ?? null,
    parent_id: source.parent_id ?? null,
    population: source.population ?? null,
    latitude: source.latitude ?? baseCity.latitude ?? null,
    longitude: source.longitude ?? baseCity.longitude ?? null,
    timezone: source.timezone ?? baseCity.timezone ?? null,
    wikiDataId: source.wikiDataId ?? null,
    country_code: countryCode,
    state_code: stateCode,
    state_id: source.state_id ?? baseCity.state_id ?? null,
    country_id: source.country_id ?? baseCity.country_id ?? null,
  };
}

function createWriteQueue(limit) {
  const maxConcurrent = Math.max(1, limit);
  const executing = new Set();
  let firstError = null;

  const enqueue = async (task) => {
    if (firstError) {
      throw firstError;
    }

    let taskPromise;
    taskPromise = Promise.resolve()
      .then(task)
      .catch((error) => {
        if (!firstError) {
          firstError = error;
        }
        throw error;
      })
      .finally(() => {
        executing.delete(taskPromise);
      });

    executing.add(taskPromise);

    if (executing.size >= maxConcurrent) {
      await Promise.race(executing).catch(() => {});
      if (firstError) {
        throw firstError;
      }
    }
  };

  const flush = async () => {
    await Promise.allSettled(Array.from(executing));
    if (firstError) {
      throw firstError;
    }
  };

  return { enqueue, flush };
}

function createDirectoryEnsurer() {
  const ensured = new Set();
  return async (dirPath) => {
    if (ensured.has(dirPath)) {
      return;
    }
    await ensureDirectory(dirPath);
    ensured.add(dirPath);
  };
}

async function processCountriesChunk({
  language,
  chunkCountries,
  stateById,
  cityById,
  writeConcurrency,
  dataRoot,
}) {
  const ensureDir = createDirectoryEnsurer();
  const writeQueue = createWriteQueue(writeConcurrency);
  const languageDir = path.join(dataRoot, language);
  await ensureDir(languageDir);

  const countryCodes = [];
  let stateCount = 0;
  let cityCount = 0;

  for (const country of chunkCountries) {
    const countryCode = sanitizePathSegment(
      country.iso2,
      `country-${country.id ?? "unknown"}`
    );
    const countryDir = path.join(languageDir, countryCode);
    await ensureDir(countryDir);

    const countryDetail = buildCountryDetail(country, language);
    const states = Array.isArray(country.states) ? country.states : [];
    const stateCodes = [];

    for (const baseState of states) {
      const translatedState = stateById.get(String(baseState.id)) || null;
      const stateDetail = buildStateDetail(
        baseState,
        translatedState,
        countryCode,
        language
      );
      const stateCode = sanitizePathSegment(
        stateDetail.code,
        `state-${stateDetail.id ?? "unknown"}`
      );
      stateDetail.code = stateCode;
      stateCodes.push(stateCode);
      stateCount += 1;

      const cities = Array.isArray(baseState.cities) ? baseState.cities : [];
      const cityPayloads = [];

      for (const baseCity of cities) {
        const translatedCity = cityById.get(String(baseCity.id)) || null;
        const cityDetail = buildCityDetail(
          baseCity,
          translatedCity,
          countryCode,
          stateCode,
          language
        );

        cityCount += 1;
        cityPayloads.push(cityDetail);
      }

      const stateDir = path.join(countryDir, stateCode);
      await ensureDir(stateDir);

      const stateFilePath = path.join(stateDir, "index.json");
      const statePayload = {
        locale: language,
        country: countryDetail,
        state: stateDetail,
        cities: cityPayloads,
      };
      await writeQueue.enqueue(() => writeJsonFile(stateFilePath, statePayload));
    }

    const countryFilePath = path.join(countryDir, "index.json");
    const countryPayload = {
      locale: language,
      country: countryDetail,
      states: getUniqueSorted(stateCodes),
    };
    await writeQueue.enqueue(() => writeJsonFile(countryFilePath, countryPayload));
    countryCodes.push(countryCode);
  }

  await writeQueue.flush();

  return {
    countryCodes,
    countries: countryCodes.length,
    states: stateCount,
    cities: cityCount,
  };
}

function splitIntoChunks(items, chunkCount) {
  const count = Math.max(1, Math.min(chunkCount, items.length));
  const chunks = Array.from({ length: count }, () => []);
  for (let i = 0; i < items.length; i += 1) {
    chunks[i % count].push(items[i]);
  }
  return chunks.filter((chunk) => chunk.length > 0);
}

function buildWorkerPayloads({
  language,
  countries,
  workerCount,
  stateById,
  cityById,
  writeConcurrency,
  dataRoot,
}) {
  const chunks = splitIntoChunks(countries, workerCount);
  const payloads = [];

  for (const chunkCountries of chunks) {
    const stateTranslations = {};
    const cityTranslations = {};

    for (const country of chunkCountries) {
      const states = Array.isArray(country.states) ? country.states : [];
      for (const state of states) {
        const stateId = String(state.id);
        if (!stateTranslations[stateId]) {
          const translatedState = stateById.get(stateId);
          if (translatedState) {
            stateTranslations[stateId] = translatedState;
          }
        }

        const cities = Array.isArray(state.cities) ? state.cities : [];
        for (const city of cities) {
          const cityId = String(city.id);
          if (!cityTranslations[cityId]) {
            const translatedCity = cityById.get(cityId);
            if (translatedCity) {
              cityTranslations[cityId] = translatedCity;
            }
          }
        }
      }
    }

    payloads.push({
      language,
      chunkCountries,
      stateTranslations,
      cityTranslations,
      writeConcurrency,
      dataRoot,
    });
  }

  return payloads;
}

function runWorker(payload) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(__filename, {
      workerData: payload,
    });

    worker.on("message", (message) => {
      if (message?.type === "result") {
        resolve(message.result);
      } else if (message?.type === "error") {
        reject(new Error(message.error || "Worker failed"));
      }
    });

    worker.on("error", reject);

    worker.on("exit", (code) => {
      if (code !== 0) {
        reject(new Error(`Worker exited with code ${code}`));
      }
    });
  });
}

async function resetLanguageOutput(language) {
  const languageDir = path.join(DATA_ROOT, language);
  const legacyLanguageIndexPath = path.join(DATA_ROOT, `${language}.json`);

  await fsp.rm(languageDir, { recursive: true, force: true });
  await fsp.rm(legacyLanguageIndexPath, { force: true });
  await ensureDirectory(languageDir);
}

async function generateLanguageData(language, countries, stateById, cityById) {
  await resetLanguageOutput(language);

  const workerCount = resolveWorkerCount(countries.length);
  const totalWriteConcurrency = resolveWriteConcurrency(workerCount);
  const perWorkerWriteConcurrency = Math.max(
    32,
    Math.ceil(totalWriteConcurrency / workerCount)
  );
  const useWorkers = workerCount > 1;

  if (!useWorkers) {
    const singleResult = await processCountriesChunk({
      language,
      chunkCountries: countries,
      stateById,
      cityById,
      writeConcurrency: perWorkerWriteConcurrency,
      dataRoot: DATA_ROOT,
    });
    const languageIndexPath = path.join(DATA_ROOT, language, "index.json");
    await writeJsonFile(languageIndexPath, getUniqueSorted(singleResult.countryCodes));
    return {
      countries: singleResult.countries,
      states: singleResult.states,
      cities: singleResult.cities,
    };
  }

  rlog.info(
    `Locale ${language}: workers=${workerCount}, totalWriteConcurrency=${totalWriteConcurrency}, perWorkerWriteConcurrency=${perWorkerWriteConcurrency}`
  );

  const payloads = buildWorkerPayloads({
    language,
    countries,
    workerCount,
    stateById,
    cityById,
    writeConcurrency: perWorkerWriteConcurrency,
    dataRoot: DATA_ROOT,
  });

  const workerResults = await Promise.all(payloads.map((payload) => runWorker(payload)));

  const allCountryCodes = [];
  let totalCountries = 0;
  let totalStates = 0;
  let totalCities = 0;

  for (const result of workerResults) {
    totalCountries += result.countries;
    totalStates += result.states;
    totalCities += result.cities;
    allCountryCodes.push(...result.countryCodes);
  }

  const languageIndexPath = path.join(DATA_ROOT, language, "index.json");
  await writeJsonFile(languageIndexPath, getUniqueSorted(allCountryCodes));

  return {
    countries: totalCountries,
    states: totalStates,
    cities: totalCities,
  };
}

function downloadFileWithProgress(url, destinationPath, label) {
  return new Promise((resolve, reject) => {
    const ONE_MB = 1024 * 1024;
    const tmpPath = `${destinationPath}.download`;

    const request = (targetUrl) => {
      https
        .get(targetUrl, (response) => {
          if (
            response.statusCode &&
            response.statusCode >= 300 &&
            response.statusCode < 400 &&
            response.headers.location
          ) {
            response.resume();
            request(response.headers.location);
            return;
          }

          if (response.statusCode !== 200) {
            response.resume();
            reject(
              new Error(
                `Download failed (${label}) with status ${response.statusCode}`
              )
            );
            return;
          }

          const totalBytes = Number(response.headers["content-length"] || 0);
          const totalMB =
            totalBytes > 0 ? Math.max(Math.ceil(totalBytes / ONE_MB), 1) : 0;
          let downloadedBytes = 0;
          let lastReportedMB = -1;

          const fileStream = fs.createWriteStream(tmpPath);

          response.on("data", (chunk) => {
            downloadedBytes += chunk.length;
            if (totalMB > 0) {
              const downloadedMB = Math.min(
                Math.floor(downloadedBytes / ONE_MB),
                totalMB
              );
              if (downloadedMB !== lastReportedMB) {
                rlog.progress(downloadedMB, totalMB);
                lastReportedMB = downloadedMB;
              }
            } else {
              const downloadedMB = Math.max(
                Math.floor(downloadedBytes / ONE_MB),
                0
              );
              if (downloadedMB !== lastReportedMB) {
                rlog.progress(downloadedMB, downloadedMB + 1);
                lastReportedMB = downloadedMB;
              }
            }
          });

          response.pipe(fileStream);

          fileStream.on("finish", async () => {
            fileStream.close(async () => {
              try {
                if (totalMB > 0) {
                  rlog.progress(totalMB, totalMB);
                }
                await fsp.rename(tmpPath, destinationPath);
                const finalSize = (await fsp.stat(destinationPath)).size;
                rlog.success(
                  `Downloaded ${label}: ${formatMB(finalSize)} MB -> ${destinationPath}`
                );
                resolve();
              } catch (error) {
                await fsp.unlink(tmpPath).catch(() => {});
                reject(error);
              }
            });
          });

          response.on("error", async (error) => {
            fileStream.destroy();
            await fsp.unlink(tmpPath).catch(() => {});
            reject(error);
          });

          fileStream.on("error", async (error) => {
            response.destroy();
            await fsp.unlink(tmpPath).catch(() => {});
            reject(error);
          });
        })
        .on("error", reject);
    };

    request(url);
  });
}

async function ensureDecompressedFile(gzipPath, outputPath) {
  let shouldDecompress = !exists(outputPath);
  if (!shouldDecompress) {
    const [gzStat, outputStat] = await Promise.all([
      fsp.stat(gzipPath),
      fsp.stat(outputPath),
    ]);
    shouldDecompress = gzStat.mtimeMs > outputStat.mtimeMs;
  }

  if (!shouldDecompress) {
    return;
  }

  const tmpPath = `${outputPath}.tmp`;
  await pipeline(
    fs.createReadStream(gzipPath),
    zlib.createGunzip(),
    fs.createWriteStream(tmpPath)
  );
  await fsp.rename(tmpPath, outputPath);
  const outputSize = (await fsp.stat(outputPath)).size;
  rlog.info(`Decompressed cities source: ${formatMB(outputSize)} MB -> ${outputPath}`);
}

async function ensureSourceFiles() {
  await ensureDirectory(CACHE_ROOT);

  if (!exists(CACHE_FILES.countries)) {
    rlog.info("Cache miss: countries-states-cities");
    await downloadFileWithProgress(
      SOURCE_URLS.countries,
      CACHE_FILES.countries,
      "countries-states-cities.json"
    );
  } else {
    const size = (await fsp.stat(CACHE_FILES.countries)).size;
    rlog.info(`Using cached countries file: ${formatMB(size)} MB`);
  }

  if (!exists(CACHE_FILES.states)) {
    rlog.info("Cache miss: states");
    await downloadFileWithProgress(
      SOURCE_URLS.states,
      CACHE_FILES.states,
      "states.json"
    );
  } else {
    const size = (await fsp.stat(CACHE_FILES.states)).size;
    rlog.info(`Using cached states file: ${formatMB(size)} MB`);
  }

  if (!exists(CACHE_FILES.citiesGz)) {
    rlog.info("Cache miss: cities gzip");
    await downloadFileWithProgress(
      SOURCE_URLS.citiesGz,
      CACHE_FILES.citiesGz,
      "cities.json.gz"
    );
  } else {
    const size = (await fsp.stat(CACHE_FILES.citiesGz)).size;
    rlog.info(`Using cached cities gzip file: ${formatMB(size)} MB`);
  }

  await ensureDecompressedFile(CACHE_FILES.citiesGz, CACHE_FILES.cities);

  return {
    countriesPath: CACHE_FILES.countries,
    statesPath: CACHE_FILES.states,
    citiesPath: CACHE_FILES.cities,
  };
}

async function parseJsonFromFile(filePath) {
  const raw = await fsp.readFile(filePath, "utf8");
  return JSON.parse(raw);
}

async function removeLegacySourceDirectory() {
  if (exists(LEGACY_SOURCE_ROOT)) {
    await fsp.rm(LEGACY_SOURCE_ROOT, { recursive: true, force: true });
    rlog.info(`Removed legacy source directory: ${LEGACY_SOURCE_ROOT}`);
  }
}

async function loadDatasets() {
  const sourcePaths = await ensureSourceFiles();
  await removeLegacySourceDirectory();

  rlog.info("Loading source files into memory");
  const [countries, states, cities] = await Promise.all([
    parseJsonFromFile(sourcePaths.countriesPath),
    parseJsonFromFile(sourcePaths.statesPath),
    parseJsonFromFile(sourcePaths.citiesPath),
  ]);

  if (!Array.isArray(countries)) {
    throw new Error("countries-states-cities.json is not an array");
  }
  if (!Array.isArray(states)) {
    throw new Error("states.json is not an array");
  }
  if (!Array.isArray(cities)) {
    throw new Error("cities.json is not an array");
  }

  const stateById = new Map();
  for (const state of states) {
    stateById.set(String(state.id), state);
  }

  const cityById = new Map();
  for (const city of cities) {
    cityById.set(String(city.id), city);
  }

  rlog.info(
    `Loaded source data: countries=${countries.length}, states=${states.length}, cities=${cities.length}`
  );

  return { countries, stateById, cityById };
}

async function runWorkerThread() {
  const stateById = new Map(Object.entries(workerData.stateTranslations || {}));
  const cityById = new Map(Object.entries(workerData.cityTranslations || {}));

  const result = await processCountriesChunk({
    language: workerData.language,
    chunkCountries: workerData.chunkCountries,
    stateById,
    cityById,
    writeConcurrency: workerData.writeConcurrency,
    dataRoot: workerData.dataRoot,
  });

  parentPort.postMessage({ type: "result", result });
}

async function main() {
  const startedAt = Date.now();
  await ensureDirectory(DATA_ROOT);

  rlog.info(
    `Perf config: cpus=${LOGICAL_CPUS}, uvThreadpool=${process.env.UV_THREADPOOL_SIZE}, defaultWorkers=${DEFAULT_WORKER_COUNT}, defaultWriteConcurrency=${DEFAULT_WRITE_CONCURRENCY}`
  );

  const { countries, stateById, cityById } = await loadDatasets();
  const languageSets = discoverLanguages(countries, stateById, cityById);
  const discoveryMode = parseDiscoveryMode();
  const discoveredLanguages =
    discoveryMode === "union" ? languageSets.union : languageSets.core;
  const languages = parseRequestedLanguages(discoveredLanguages);

  if (process.argv.includes("--list-languages")) {
    rlog.info(
      `Discovered locales: core=${languageSets.core.length}, union=${languageSets.union.length}`
    );
    rlog.info(`Selected mode: ${discoveryMode}`);
    rlog.info(`Selected locales (${discoveredLanguages.length}):`);
    for (const locale of discoveredLanguages) {
      rlog.info(`- ${locale}`);
    }
    return;
  }

  rlog.info(
    `Locales selected (${languages.length}/${discoveredLanguages.length}, mode=${discoveryMode}): ${languages.join(", ")}`
  );

  const summaries = [];
  for (const language of languages) {
    rlog.info(`Generating locale data for: ${language}`);
    const summary = await generateLanguageData(
      language,
      countries,
      stateById,
      cityById
    );
    summaries.push({ language, ...summary });
    rlog.success(
      `Locale ${language} complete: ${summary.countries} countries, ${summary.states} states, ${summary.cities} cities`
    );
  }

  const indexFilePath = path.join(DATA_ROOT, "index.json");
  await writeJsonFile(indexFilePath, languages);

  const elapsed = ((Date.now() - startedAt) / 1000).toFixed(2);
  rlog.success(`All done in ${elapsed}s`);
  for (const summary of summaries) {
    rlog.info(
      `[${summary.language}] countries=${summary.countries}, states=${summary.states}, cities=${summary.cities}`
    );
  }
}

if (isMainThread) {
  main().catch((error) => {
    rlog.error(error?.stack || String(error));
    process.exitCode = 1;
  });
} else {
  runWorkerThread().catch((error) => {
    if (parentPort) {
      parentPort.postMessage({
        type: "error",
        error: error?.stack || String(error),
      });
    }
    process.exitCode = 1;
  });
}
