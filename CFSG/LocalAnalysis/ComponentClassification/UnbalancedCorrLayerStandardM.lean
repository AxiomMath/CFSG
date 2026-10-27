module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandardBM
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotBabyMonster

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG.Blueprint

theorem layerGeneratedUniversalComponentStandard_of_M
    (hM : CommutingBlockOvergroupExclusion NativeSporadic.M) :
    LayerGeneratedUniversalComponentStandard :=
  layerGeneratedUniversalComponentStandard_of_BM
    (fun _ _ _ _ hq he hJ hΔ _ hL hML hLH =>
      LocalAnalysis.ComponentInitial.commuting_block_baby_monster_overgroup_exclusion hq he hJ hΔ
        hL hML hLH)
    hM

end CFSG.ComponentClassification.UnbalancedCorr
