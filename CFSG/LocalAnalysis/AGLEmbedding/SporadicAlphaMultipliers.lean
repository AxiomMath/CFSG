module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census

theorem false_of_center_pGroup_of_not_dvd_hopfMultiplier {K X : Type} [Group K] [Finite K]
    [Group X] {p : ℕ} (hp : p.Prime) (hq : Open.IsQuasisimple K)
    (hZ : IsPGroup p (Subgroup.center K)) (hZne : Subgroup.center K ≠ ⊥)
    (e : K ⧸ Subgroup.center K ≃* X)
    (h : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier
    (KFactProofs.ThreeCover.isQuasisimple_of_open hq) e
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact hZne (Subgroup.card_eq_one.mp hk)
  · exact h ((dvd_pow_self p (Nat.succ_ne_zero k)).trans (hk ▸ hdvd))

theorem kFactAlphaConclusion_of_hopfMultiplier {K X : Type} [Group K] [Finite K] [Group X]
    (hq : Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X)) :
    KFactAlphaConclusion K := by
  intro p hp hp2 hZne hZp _ T
  exact (false_of_center_pGroup_of_not_dvd_hopfMultiplier hp hq hZp hZne e (h p hp hp2)).elim

end CFSG.AGLEmbedding
