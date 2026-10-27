module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Rank

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem aor_two_le_pRank_of_nonPocketed [Finite G] {X : Subgroup G} (hX : InFStar X)
    (hF : ¬ InF X) (hL : ¬ IsL3Eps3 X) : 2 ≤ CFSG.Open.pRank 2 X := by
  unfold InFStar IsFStarGroup at hX
  rcases hX with hF' | ⟨hq, hstar⟩
  · exact absurd hF' hF
  · unfold SmallF3StarQuotient at hstar
    rcases hstar with h | h | h | h
    · exact sec63_two_le_pRank hq (Or.inl h)
    · exact sec63_two_le_pRank hq (Or.inr h)
    · exact absurd (Or.inl h) hL
    · exact absurd (Or.inr h) hL

end CFSG.OddStandard.SmallF3.Omega
