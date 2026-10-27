module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open CFSG.Blueprint CFSG.RankThree.OuterOrder
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_range_conj_of_odd_orderOf_of_card_outer_dvd {T : Type} [Group T] {k : ℕ}
    (hout : Nat.card (Outer T) ∣ 2 ^ k) {σ : MulAut T} (hσ : Odd (orderOf σ)) :
    σ ∈ (MulAut.conj : T →* MulAut T).range := by
  set π := QuotientGroup.mk' (inner T) with hπ
  have h1 : orderOf (π σ) ∣ orderOf σ := orderOf_map_dvd π σ
  have h2 : orderOf (π σ) ∣ 2 ^ k := (orderOf_dvd_natCard (π σ)).trans hout
  have hgcd : Nat.gcd (orderOf σ) (2 ^ k) = 1 :=
    (Nat.Coprime.pow_right k hσ.coprime_two_right : Nat.Coprime (orderOf σ) (2 ^ k))
  have h3 : orderOf (π σ) = 1 := Nat.dvd_one.1 (hgcd ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem card_outer_dvd_u43 {S : Type} [Group S] [Finite S] (h : LieModel S .PSU 4 3 1) :
    Nat.card (Outer S) ∣ 2 ^ 3 := by
  obtain ⟨hdvd, -⟩ := higher_linear_unitary_outer_order_determinant_bound (Or.inr rfl)
    (by norm_num : 3 ≤ 4) Nat.prime_three le_rfl (h.statedClassicalModel (by decide))
  exact hdvd.trans (by decide)

theorem card_outer_dvd_psl_three_nine {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSL 3 3 2) : Nat.card (Outer S) ∣ 2 ^ 2 := by
  obtain ⟨hdvd, -⟩ := higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
    (by norm_num : 3 ≤ 3) Nat.prime_three (by norm_num : 1 ≤ 2) (h.statedClassicalModel (by decide))
  exact hdvd.trans (by decide)

theorem card_outer_dvd_psl_four_three {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSL 4 3 1) : Nat.card (Outer S) ∣ 2 ^ 2 := by
  obtain ⟨hdvd, -⟩ := higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
    (by norm_num : 3 ≤ 4) Nat.prime_three le_rfl (h.statedClassicalModel (by decide))
  exact hdvd.trans (by decide)

theorem outNoOdd_holds : OutNoOdd := by
  intro S _ _ hS σ hσ
  rcases hS with h | h | h
  · exact mem_range_conj_of_odd_orderOf_of_card_outer_dvd (card_outer_dvd_u43 h) hσ
  · exact mem_range_conj_of_odd_orderOf_of_card_outer_dvd (card_outer_dvd_psl_three_nine h) hσ
  · exact mem_range_conj_of_odd_orderOf_of_card_outer_dvd (card_outer_dvd_psl_four_three h) hσ

end CFSG.EvenSporadicStandard.HSStd.InvCent
