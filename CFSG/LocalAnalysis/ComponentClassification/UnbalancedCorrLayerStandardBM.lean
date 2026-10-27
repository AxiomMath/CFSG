module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandardRest
public import CFSG.Sporadic.Co1Block.Block
public import CFSG.Sporadic.FischerOddCore.Fi24Block
public import CFSG.Sporadic.HNOddCore.Block

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG.Blueprint

theorem layerGeneratedUniversalComponentStandard_of_BM
    (hB : CommutingBlockOvergroupExclusion NativeSporadic.B)
    (hM : CommutingBlockOvergroupExclusion NativeSporadic.M) :
    LayerGeneratedUniversalComponentStandard :=
  layerGeneratedUniversalComponentStandard_of_remaining
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      Sporadic.Co1Block.commuting_block_co1_overgroup_exclusion hq he hJ hΔ hL hML hLH)
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      Sporadic.FischerOddCore.CTI_commuting_block_Fi24prime_overgroup_exclusion hq he hJ hΔ hL
        hML hLH)
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      Sporadic.HNOddCore.cti_commuting_block_hn_overgroup_exclusion hq he hJ hΔ hL hML hLH)
    hB hM

end CFSG.ComponentClassification.UnbalancedCorr
