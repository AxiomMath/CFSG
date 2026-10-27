module

public import CFSG.LocalAnalysis.RankFourTheoremC.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem uniqueFour_of_atCore (hpre : GLBPreuniqueness G) (hD1 : D1For G)
    (hE1 : AlmostStrongAtCore G) (hE2 : ConfinementAtCore G) : GLBUniqueFour G :=
  glbUniqueFour_iff.mpr ⟨almostStrongMaximalLocals_of_atCore hpre hD1 hE1,
    rankTwoConfinement_of_atCore hpre hD1 hE2⟩

theorem theoremCRankFour_of_endpoints (hD1 : D1Rank4) (hE1 : E1Rank4) (hE2 : E2Rank4)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hpre : GLBPreuniqueness G) : GLBUniqueFour G :=
  uniqueFour_of_atCore hpre (hD1 G hnonab hK hchar he hpre) (hE1 G hnonab hK hchar he hpre)
    (hE2 G hnonab hK hchar he hpre)

end CFSG.LocalAnalysis.RankFourTheoremC
