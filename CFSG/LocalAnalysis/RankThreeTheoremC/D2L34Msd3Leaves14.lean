module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Leaves13
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Cited

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem D2Leaves3SW.toLeaves3S_of_cited (hK : D2KFactLeaves) (hAut : KFactStrongThreeAutomizer)
    (hgl : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne) (hLF : LargeFieldParabolic)
    (hT : CitedBlockTransvectionPLType) (hIrr : KFactBlockOneImageIrr3) (h : D2Leaves3SW G) :
    D2Leaves3S G :=
  h.toLeaves3S (d2PairA6Residue3_of_cited hK hAut hgl hGN hCov hLF hT hIrr)

end CFSG.LocalAnalysis.RankThreeTheoremC
