module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Consumers
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291PerfHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Beta
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29InnerHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Holds

theorem kd291PPerf_holds : KD291PPerf :=
  kd291PPerf_of_gamma N3.gammaStructureP_holds
    CFSG.LocalAnalysis.RankFourTheoremC.kd29Inner_holds

theorem p622L613_holds : P622L613 :=
  p622L613_of_kd291PPerf kd291PPerf_holds noTwoComponentsGen_holds

theorem l613f3E3_holds : L613f3E3 :=
  N3.l613f3E3_of_kd291PPerf kd291PPerf_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds GL83.I_6_10_1_proved
    GL83.I713.i_7_13_1_holds K713S.kFactSylowSplit_holds
    CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved

theorem slotLemma630FiveCond_of_prop65 (h65 : SlotProp65Five) : SlotLemma630FiveCond :=
  slotLemma630FiveCond_of_residues h65 kFactI2026_holds l613f3E3_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
