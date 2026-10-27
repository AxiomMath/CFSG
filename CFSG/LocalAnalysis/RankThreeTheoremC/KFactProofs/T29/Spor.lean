module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Families
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporON
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.Coordinator

section SporCertified


theorem t29Spor_holds
    : T29Spor := by
  intro X _ _ L x h ⟨s, ⟨e⟩⟩
  exfalso
  have hq : CFSG.Open.IsQuasisimple ↥L := h.comp.2.2
  have hout : Nat.card (Outer (↥L ⧸ center ↥L)) ≤ 2 :=
    card_outer_centerQuotient_le_two CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      hq ⟨s, ⟨e⟩⟩
  have hin := aut_three_inner_of_outer_le_two hout
  have hdec : ∀ g : X, g ^ 3 = 1 → ∃ l ∈ L, ∃ c ∈ centralizer (L : Set X), g = l * c :=
    fun g hg => h.exists_mul_of_inner (MulEquiv.refl _) hin hg
  by_cases hZ : center ↥L = ⊥
  · by_cases hJ : s = .J3
    · subst hJ
      exact h.false_of_center_bot_cent hZ hdec (MulEquiv.refl _)
        (fun y hy => j3_three_le_pRank_centralizer _ e y hy)
    · exact sporadic_three_rank_ne_three s hJ e (h.pRank_quotient_eq_three hZ hout)
  · obtain ⟨hcard3, hs⟩ := h.card_center_spor
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
      hZ e
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZc : IsCyclic ↥(center ↥L) := isCyclic_of_prime_card hcard3
    have hO := h.isCyclic_pCore_of_center_cyclic hZc hZ
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.false_of_abelian_bound hO hcard3 hdec
        (fun A hA hcomm => abelian_three_card_le_nine_hatM22 h.comp.2.2.1 hcard3 e A hA hcomm)
    · exact h.false_of_cover_J3 hcard3 e
    · exact h.false_of_cover_McL hcard3 e
    · exact h.false_of_cover_Suz hcard3 e
    · obtain ⟨hr, hc⟩ := on_cover_data hq hcard3 ⟨e⟩
      exact h.false_of_triple_cover hO hcard3 hdec hr hc
    · exact h.false_of_cover_Fi22 hcard3 e
    · exact h.false_of_cover_Fi24Prime hcard3 e

end SporCertified

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
