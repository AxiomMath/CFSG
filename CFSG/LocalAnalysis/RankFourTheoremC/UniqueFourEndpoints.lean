module

public import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem confinementAtCore_of_uniqueFour (h : GLBUniqueFour G) : ConfinementAtCore G :=
  confinementAtCore_of_rankTwoConfinement (glbUniqueFour_iff.1 h).2

end CFSG.LocalAnalysis.RankFourTheoremC
