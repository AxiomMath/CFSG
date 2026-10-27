module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSevenLocal
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbedding

theorem kFactBlockInvertedThree_of_hP2 (h93 : Asc81bNineThree) (h86 : Asc81bEightSix)
    (hTPLT : CitedBlockTransvectionPLType) (hP2 : KFactParabolicThreeInv) :
    KFactBlockInvertedThree :=
  kFactBlockInvertedThree_of h93 h86 hTPLT hP2
    (citedBlockAltSevenInv_of h86 kFactAltSevenTwoLocalInv_holds)


theorem kFactBlockInvertedThree_holds (h93 : Asc81bNineThree)
    (hTPLT : CitedBlockTransvectionPLType) : KFactBlockInvertedThree :=
  kFactBlockInvertedThree_of_hP2 h93
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved) hTPLT
    kFactParabolicThreeInv_holds

end CFSG.AGLEmbedding
