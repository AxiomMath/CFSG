module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator


theorem kFactSPLBlockTorusCaseB_of_lie (hRest : KFactSPLBlockTorusCaseBLie) :
    CFSG.HardMathSupport.Curtis.Proving.KFactSPLBlockTorusCaseB :=
  caseB_of_lie_rest CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds hRest

theorem kFactSPLBlockTorus_of_lie (hRest : KFactSPLBlockTorusCaseBLie) :
    CFSG.AGLEmbedding.KFactSPLBlockTorus :=
  CFSG.HardMathSupport.Curtis.Proving.kFactSPLBlockTorus_of_caseB
    (kFactSPLBlockTorusCaseB_of_lie hRest)

end CFSG.HardMathSupport.Curtis.Coordinator
