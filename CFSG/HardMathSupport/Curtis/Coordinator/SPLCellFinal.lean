module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFam
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorus

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

theorem splLieInnerCell_of_open_families (hA : SPLLieInnerCellFam IsIdxA)
    (hTA : SPLLieInnerCellFam IsIdxTwistedA) (hD : SPLLieInnerCellFam IsIdxD)
    (hTD : SPLLieInnerCellFam IsIdxTwistedD) (hG : SPLLieInnerCellFam IsIdxG2) :
    SPLLieInnerCell :=
  splLieInnerCell_of_families hA hTA splLieInnerCellFam_B hD hTD hG


theorem kFactSPLBlockTorus_of_open_families (hA : SPLLieInnerCellFam IsIdxA)
    (hTA : SPLLieInnerCellFam IsIdxTwistedA) (hD : SPLLieInnerCellFam IsIdxD)
    (hTD : SPLLieInnerCellFam IsIdxTwistedD) (hG : SPLLieInnerCellFam IsIdxG2) :
    CFSG.AGLEmbedding.KFactSPLBlockTorus :=
  kFactSPLBlockTorus_of_lie
    (kFactSPLBlockTorusCaseBLie_of_cell (splLieInnerCell_of_open_families hA hTA hD hTD hG))

end CFSG.HardMathSupport.Curtis.Coordinator
