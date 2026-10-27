module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Leaves15
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycE

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaMSolvableR9.toStrong3_of_nodes
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hX : D1NoXBlock3 G) (h : D2L34BetaMSolvableR9 G) : D2L34BetaMSolvableStrong3 G :=
  h.toStrong3 hFF hI59 hX (ffCyclicInput3W_of_nodes hX)

structure D2Leaves3SZ (G : Type) [Group G] [Finite G] : Prop where
  l34MSolvable : D2L34BetaMSolvableR9 G

theorem D2Leaves3SZ.toLeaves3SX
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59) (hX : D1NoXBlock3 G) (h : D2Leaves3SZ G) :
    D2Leaves3SX G :=
  ⟨h.l34MSolvable.toStrong3_of_nodes hFF hI59 hX⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
