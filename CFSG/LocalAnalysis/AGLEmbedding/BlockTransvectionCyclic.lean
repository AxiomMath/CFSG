module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicCenter
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbedding

theorem citedBlockTransvectionCyclic_holds
    (hTPLT : CitedBlockTransvectionPLType) : CitedBlockTransvectionCyclic :=
  citedBlockTransvectionCyclic_of_PLType
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved) hTPLT

end CFSG.AGLEmbedding
