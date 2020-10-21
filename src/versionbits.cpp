// Copyright (c) 2016-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <versionbits.h>
#include <consensus/params.h>

template<typename CondFn>
static ThresholdState BIP8Transitions(ThresholdState prev_state, const CBlockIndex* pindexPrev, int64_t height_start, int64_t height_timeout, bool lockinontimeout, int threshold, int period, CondFn& condition)
{
    // We track state by previous-block, so the height we should be comparing is +1
    assert(pindexPrev != nullptr);
    const int64_t height = pindexPrev->nHeight + 1;

    switch (prev_state) {
    case ThresholdState::DEFINED:
        if (height >= height_start) {
            return ThresholdState::STARTED;
        }
        return ThresholdState::DEFINED;

    case ThresholdState::STARTED: {
        const CBlockIndex* pindexCount = pindexPrev;
        int count = 0;
        for (int i = 0; pindexCount != nullptr && i < period; ++i) {
            if (condition(pindexCount)) {
                count++;
            }
            pindexCount = pindexCount->pprev;
        }

        if (count >= threshold) {
            return ThresholdState::LOCKED_IN;
        } else if (lockinontimeout && height + period >= height_timeout) {
            return ThresholdState::MUST_SIGNAL;
        } else if (height >= height_timeout) {
            return ThresholdState::FAILED;
        }
        return ThresholdState::STARTED;
    }

    case ThresholdState::MUST_SIGNAL:
        // Always progresses into LOCKED_IN.
        return ThresholdState::LOCKED_IN;

    case ThresholdState::LOCKED_IN:
        // Always progresses into ACTIVE.
        return ThresholdState::ACTIVE;

    // Terminal states.
    case ThresholdState::ACTIVE:
        return ThresholdState::ACTIVE;

    case ThresholdState::FAILED:
        return ThresholdState::FAILED;
    } // no default case, so the compiler can warn about missing cases

    return prev_state;
}

static bool BIP8Trivial(ThresholdState& state, const CBlockIndex* pindexPrev, int64_t height_start, int64_t height_timeout, bool lockinontimeout, int threshold, int period)
{
    // Check if this deployment is always active.
    if (height_start == Consensus::VBitsDeployment::ALWAYS_ACTIVE) {
        state = ThresholdState::ACTIVE;
        return true;
    }

    if (pindexPrev == nullptr) {
        state = ThresholdState::DEFINED;
        return true;
    }

    // Check if this deployment is never active.
    if (height_start == Consensus::VBitsDeployment::NEVER_ACTIVE && height_timeout == Consensus::VBitsDeployment::NEVER_ACTIVE ) {
        state = ThresholdState::FAILED;
        return true;
    }

    if (pindexPrev->nHeight + 1 < height_start) {
        // Optimization: don't recompute down further, as we know every earlier block will be before the start height
        state = ThresholdState::DEFINED;
        return true;
    }

    return false;
}

ThresholdState AbstractThresholdConditionChecker::GetStateFor(const CBlockIndex* pindexPrev, ThresholdConditionCache& cache) const
{
    int nPeriod = Period();
    int nThreshold = Threshold();
    int64_t height_start = StartHeight();
    int64_t height_timeout = TimeoutHeight();
    const bool lockinontimeout = LockinOnTimeout();

    // A block's state is always the same as that of the first of its period, so it is computed based on a pindexPrev whose height equals a multiple of nPeriod - 1.
    if (pindexPrev != nullptr) {
        pindexPrev = pindexPrev->GetAncestor(pindexPrev->nHeight - ((pindexPrev->nHeight + 1) % nPeriod));
    }

    // Walk backwards in steps of nPeriod to find a pindexPrev whose information is known
    std::vector<const CBlockIndex*> vToCompute;
    ThresholdState state;

    while (!BIP8Trivial(state, pindexPrev, height_start, height_timeout, lockinontimeout, nThreshold, nPeriod)) {
        assert(pindexPrev != nullptr); // BIP8Trivial handles that case
        if (cache.count(pindexPrev) > 0) {
            state = cache[pindexPrev];
            break;
        }
        vToCompute.push_back(pindexPrev);
        pindexPrev = pindexPrev->GetAncestor(pindexPrev->nHeight - nPeriod);
    }

    // At this point, state has been initialised either by BIP8Trivial or from
    // a previously cached value, and vToCompute has the states we need to calculate
    // and cache

    // Now walk forward and compute the state of descendants of pindexPrev
    while (!vToCompute.empty()) {
        pindexPrev = vToCompute.back();
        vToCompute.pop_back();

        auto cond = [this](const CBlockIndex* pindexPrev) { return Condition(pindexPrev); };

        cache[pindexPrev] = state = BIP8Transitions(state, pindexPrev, height_start, height_timeout, lockinontimeout, nThreshold, nPeriod, cond);
    }

    return state;
}

VBitsStats AbstractThresholdConditionChecker::GetStateStatisticsFor(const CBlockIndex* pindex) const
{
    VBitsStats stats = {};

    stats.period = Period();
    stats.threshold = Threshold();

    if (pindex == nullptr)
        return stats;

    // Find beginning of period
    const CBlockIndex* pindexEndOfPrevPeriod = pindex->GetAncestor(pindex->nHeight - ((pindex->nHeight + 1) % stats.period));
    stats.elapsed = pindex->nHeight - pindexEndOfPrevPeriod->nHeight;

    // Count from current block to beginning of period
    int count = 0;
    const CBlockIndex* currentIndex = pindex;
    while (pindexEndOfPrevPeriod->nHeight != currentIndex->nHeight){
        if (Condition(currentIndex))
            count++;
        currentIndex = currentIndex->pprev;
    }

    stats.count = count;
    stats.possible = (stats.period - stats.threshold ) >= (stats.elapsed - count);

    return stats;
}

int AbstractThresholdConditionChecker::GetStateSinceHeightFor(const CBlockIndex* pindexPrev, ThresholdConditionCache& cache) const
{
    int64_t height_start = StartHeight();
    if (height_start == Consensus::VBitsDeployment::ALWAYS_ACTIVE) {
        return 0;
    }

    const ThresholdState initialState = GetStateFor(pindexPrev, cache);

    // BIP 8 about state DEFINED: "The genesis block is by definition in this state for each deployment."
    if (initialState == ThresholdState::DEFINED) {
        return 0;
    }

    const int nPeriod = Period();

    // A block's state is always the same as that of the first of its period, so it is computed based on a pindexPrev whose height equals a multiple of nPeriod - 1.
    // To ease understanding of the following height calculation, it helps to remember that
    // right now pindexPrev points to the block prior to the block that we are computing for, thus:
    // if we are computing for the last block of a period, then pindexPrev points to the second to last block of the period, and
    // if we are computing for the first block of a period, then pindexPrev points to the last block of the previous period.
    // The parent of the genesis block is represented by nullptr.
    pindexPrev = pindexPrev->GetAncestor(pindexPrev->nHeight - ((pindexPrev->nHeight + 1) % nPeriod));

    const CBlockIndex* previousPeriodParent = pindexPrev->GetAncestor(pindexPrev->nHeight - nPeriod);

    while (previousPeriodParent != nullptr && GetStateFor(previousPeriodParent, cache) == initialState) {
        pindexPrev = previousPeriodParent;
        previousPeriodParent = pindexPrev->GetAncestor(pindexPrev->nHeight - nPeriod);
    }

    // Adjust the result because right now we point to the parent block.
    return pindexPrev->nHeight + 1;
}

namespace
{
/**
 * Class to implement versionbits logic.
 */
class VersionBitsConditionChecker : public AbstractThresholdConditionChecker {
private:
    const Consensus::Params& params;
    const Consensus::DeploymentPos id;

protected:
    int64_t StartHeight() const override { return params.vDeployments[id].startheight; }
    int64_t TimeoutHeight() const override { return params.vDeployments[id].timeoutheight; }
    bool LockinOnTimeout() const override { return params.vDeployments[id].lockinontimeout; }
    int Period() const override { return params.nMinerConfirmationWindow; }
    int Threshold() const override { return params.nRuleChangeActivationThreshold; }

    bool Condition(const CBlockIndex* pindex) const override
    {
        return (((pindex->nVersion & VERSIONBITS_TOP_MASK) == VERSIONBITS_TOP_BITS) && (pindex->nVersion & Mask()) != 0);
    }

public:
    explicit VersionBitsConditionChecker(const Consensus::Params& params_, Consensus::DeploymentPos id_) : params(params_), id(id_) {}
    uint32_t Mask() const { return ((uint32_t)1) << params.vDeployments[id].bit; }
};

} // namespace

ThresholdState VersionBitsState(const CBlockIndex* pindexPrev, const Consensus::Params& params, Consensus::DeploymentPos pos, VersionBitsCache& cache)
{
    return VersionBitsConditionChecker(params, pos).GetStateFor(pindexPrev, cache.caches[pos]);
}

VBitsStats VersionBitsStatistics(const CBlockIndex* pindex, const Consensus::Params& params, Consensus::DeploymentPos pos)
{
    return VersionBitsConditionChecker(params, pos).GetStateStatisticsFor(pindex);
}

int VersionBitsStateSinceHeight(const CBlockIndex* pindexPrev, const Consensus::Params& params, Consensus::DeploymentPos pos, VersionBitsCache& cache)
{
    return VersionBitsConditionChecker(params, pos).GetStateSinceHeightFor(pindexPrev, cache.caches[pos]);
}

uint32_t VersionBitsMask(const Consensus::Params& params, Consensus::DeploymentPos pos)
{
    return VersionBitsConditionChecker(params, pos).Mask();
}

void VersionBitsCache::Clear()
{
    for (unsigned int d = 0; d < Consensus::MAX_VERSION_BITS_DEPLOYMENTS; d++) {
        caches[d].clear();
    }
}
