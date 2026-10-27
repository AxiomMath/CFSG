module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812CaseTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneFourCoverProof

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15


theorem p812Gen_holds
    : P812Gen :=
  p812Gen_of_inputs
    (CFSG.LocalAnalysis.RankThreeUC.AGL81C.sevenOneFourCover_of_outCyclic
      CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds)
    Section8.kFactFieldAutThree_holds Section8.kFactFieldAutInvert_holds

theorem p812_holds
    : CFSG.LocalAnalysis.RankThreeUC.S15.P812 :=
  p812_of_gen p812Gen_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
