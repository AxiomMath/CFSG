module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291PerfHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Beta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Single
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65Gamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L617
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4U0Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5OmegaU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Holds

theorem slotP614NormalizerRankLarge_holds : SlotP614NormalizerRankLarge :=
  slotP614NormalizerRankLarge_of_kfacts noTwoComponentsGen_holds
      (kFactSingleW_of_gamma N3.gammaStructureP_holds)

theorem kFactSingleW_holds : KFactSingleW :=
  kFactSingleW_of_gamma N3.gammaStructureP_holds

theorem kFactP65SingleE3_holds : N1.KFactP65SingleE3 :=
  kFactP65SingleE3_of_single kFactSingleW_holds noTwoComponentsPlane_holds

theorem slotP614LargeD2_of_coreU0 (hcore : SlotP614CoreLargeU0) : SlotP614LargeD2 :=
  slotP614LargeD2_of_stepsU0 slotP614NormalizerRankLarge_holds.toU0
    slotP614StepL617Large_holds.toU0 slotP614OmegaULarge_holds hcore

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
