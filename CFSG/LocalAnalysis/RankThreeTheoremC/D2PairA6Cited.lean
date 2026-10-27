module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Lie
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Census
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Atlas
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem d2PairA6Residue3U_of_cited (hK : D2KFactLeaves) (hAut : KFactStrongThreeAutomizer)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne) (hLF : LargeFieldParabolic)
    (hT : CitedBlockTransvectionPLType) (hIrr : KFactBlockOneImageIrr3) :
    D2PairA6Residue3U G :=
  d2PairA6Residue3U_of_inputs hK.eightFour hK.eightFive hK.eightSix hK.nineThree hK.noXBlock3
    hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven hAut
    (pairOneImageLieTR3_of_gl83 hK.noXBlock3 hK.eightFive hLF smallRankAtlas_proved hGN hCov hgl)
    (pairBlockType3_of_cited hK.nineThree hK.eightFive hK.noXBlock3 hT) hIrr

theorem d2PairA6Residue3_of_cited (hK : D2KFactLeaves) (hAut : KFactStrongThreeAutomizer)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne) (hLF : LargeFieldParabolic)
    (hT : CitedBlockTransvectionPLType) (hIrr : KFactBlockOneImageIrr3) :
    D2PairA6Residue3 G :=
  (d2PairA6Residue3U_of_cited hK hAut hgl hGN hCov hLF hT hIrr).toOld

end CFSG.LocalAnalysis.RankThreeTheoremC
