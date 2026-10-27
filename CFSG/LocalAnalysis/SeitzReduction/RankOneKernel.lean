module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStar
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarL2
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarSz

public section

namespace CFSG.SeitzReduction.RankOne


theorem hypothesisOneStar_of_seitzRankOne {X : Type} [Group X] [Finite X]
    (h : SeitzRankOne X) : HypothesisOneStar X := by
  rcases h with ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hm⟩
  · rcases hm with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · exact hypothesisOneStar_of_statedPSL2 hf hc
    all_goals exact absurd hn (by decide)
  · rcases hm with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · exact hypothesisOneStar_of_statedPSU3 hf hc
    all_goals exact absurd hn (by decide)
  · exact hypothesisOneStar_of_lieModel_twistedB2 hm

theorem card_sylow_eq_two_of_seitzRankOne {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) (h1 : SeitzRankOne L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) : Nat.card S = 2 := by
  have hZ := h.center_eq_bot
  exact card_sylow_eq_two_of_standard_star h.standardSetting hZ
    (hypothesisOneStar_of_mulEquiv (quotientCenterMulEquiv hZ).symm
      (hypothesisOneStar_of_seitzRankOne h1)) S

theorem rankOneKernel : RankOneKernel :=
  fun _ _ _ _ h h1 S => card_sylow_eq_two_of_seitzRankOne h h1 S

end CFSG.SeitzReduction.RankOne
