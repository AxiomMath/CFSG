module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandard
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotThompson
public import CFSG.Sporadic.SmallOddCore.HSBlock
public import CFSG.Sporadic.SmallOddCore.HeBlock

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG.Blueprint

theorem layerGeneratedUniversalComponentStandard_of_remaining
    (hCo1 : CommutingBlockOvergroupExclusion NativeSporadic.Co1)
    (hFi24 : CommutingBlockOvergroupExclusion NativeSporadic.Fi24prime)
    (hHN : CommutingBlockOvergroupExclusion NativeSporadic.HN)
    (hB : CommutingBlockOvergroupExclusion NativeSporadic.B)
    (hM : CommutingBlockOvergroupExclusion NativeSporadic.M) :
    LayerGeneratedUniversalComponentStandard :=
  layerGeneratedUniversalComponentStandard_of_exclusions
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      Sporadic.SmallOddCore.commuting_block_hs_overgroup_exclusion hq he hJ hΔ hL hML hLH)
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      Sporadic.SmallOddCore.commuting_block_he_overgroup_exclusion hq he hJ hΔ hL hML hLH)
    hCo1 hFi24 hHN
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      LocalAnalysis.ComponentInitial.commuting_block_thompson_overgroup_exclusion hq he hJ hΔ hL
        hML hLH)
    hB hM

end CFSG.ComponentClassification.UnbalancedCorr
