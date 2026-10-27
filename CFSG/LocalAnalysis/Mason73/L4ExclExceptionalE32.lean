module

public import CFSG.LocalAnalysis.Mason73.L4ExclClassicalE32
public import CFSG.RankThree.PartOne.SLB4A.ExcOddHcomb
public import CFSG.RankThree.PartOne.SLB4A.F4Odd
public import CFSG.RankThree.PartOne.SLB4A.TwistE6Orbit
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartOne.SLB4A CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}


theorem false_of_untwistedChevalleyModel_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h : UntwistedChevalleyModel G τ (p ^ f)) :
    False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ h
  have hneg := neg_one_ne_one_of_card_odd K (natCard_mod_two_of_eq_pow hp hp2 hK)
  rcases hτ with rfl | rfl | rfl | rfl
  · obtain ⟨U, hU, hc⟩ := exists_two_pow_five_F4_odd hneg
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc
  · obtain ⟨U, hU, hc⟩ := exists_two_pow_five_adjoint_odd _ hneg hcombE6
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc
  · obtain ⟨U, hU, hc⟩ := exists_two_pow_five_adjoint_odd _ hneg hcombE7
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc
  · obtain ⟨U, hU, hc⟩ := exists_two_pow_five_adjoint_odd _ hneg hcombE8
    exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

theorem false_of_lieModel_untwisted_E32_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    {t : CFSG.Open.StatedLieTag} {r : ℕ} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hL : LieModel G t r p f) : False := by
  have hmem : t ∈ chevalleyExceptionalTags := by
    rcases ht with rfl | rfl | rfl | rfl <;> decide
  have hm := hL.chevalleyExceptionalModel hmem
  rcases ht with rfl | rfl | rfl | rfl
  · exact false_of_untwistedChevalleyModel_of_l4Sylow hn P hP hp hp2 (Or.inl rfl) hm.2
  · exact false_of_untwistedChevalleyModel_of_l4Sylow hn P hP hp hp2 (Or.inr (Or.inl rfl)) hm.2
  · exact false_of_untwistedChevalleyModel_of_l4Sylow hn P hP hp hp2
      (Or.inr (Or.inr (Or.inl rfl))) hm.2
  · exact false_of_untwistedChevalleyModel_of_l4Sylow hn P hP hp hp2
      (Or.inr (Or.inr (Or.inr rfl))) hm.2

theorem false_of_lieModel_twistedE6_of_l4Sylow (hn : 3 ≤ n)
    (P : Sylow 2 G) (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime)
    (hp2 : p ≠ 2) {r : ℕ} (hL : LieModel G .twistedE6 r p f) : False := by
  have hm := hL.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, σ, hK, -, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 hp hm.1.2.1 hm.2
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK]
    exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left hp2).pow.pow)
  obtain ⟨U, hU, hc⟩ :=
    exists_two_pow_five_twistedE6_odd σ.toRingHom (neg_one_ne_one_of_card_odd K hodd)
  exact false_of_elementary_abelian_of_l4Sylow_of_mulEquiv hn P hP e U hc

end CFSG.LocalAnalysis.Mason73
