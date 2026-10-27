module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

theorem eq_zpowers_of_card_three_of_mem {Γ : Type*} [Group Γ] {Y : Subgroup Γ}
    (hY : Nat.card Y = 3) {c : Γ} (hc : c ∈ Y) (h3 : orderOf c = 3) :
    Subgroup.zpowers c = Y := by
  have hle : Subgroup.zpowers c ≤ Y := Subgroup.zpowers_le.mpr hc
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [hY, Nat.card_zpowers, h3]

theorem map_eq_zpowers_of_card_three_of_mem {Γ H : Type*} [Group Γ] [Group H] (e : Γ ≃* H)
    {Y : Subgroup Γ} (hY : Nat.card Y = 3) {c : H} (hc : c ∈ Y.map e.toMonoidHom)
    (h3 : orderOf c = 3) :
    Y.map e.toMonoidHom = Subgroup.zpowers c := by
  have hcard : Nat.card (Y.map e.toMonoidHom) = 3 := by
    rw [← hY]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective).toEquiv).symm
  exact (eq_zpowers_of_card_three_of_mem hcard hc h3).symm

theorem exists_zpowers_eq_of_card_three {Γ : Type*} [Group Γ] {Y : Subgroup Γ}
    (hY : Nat.card Y = 3) :
    ∃ c ∈ Y, orderOf c = 3 ∧ Subgroup.zpowers c = Y := by
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by rw [hY]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : Y)
  have hdvd : orderOf (c : Γ) ∣ 3 := by
    rw [Subgroup.orderOf_coe, ← hY]
    exact orderOf_dvd_natCard c
  have hne : orderOf (c : Γ) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    intro h
    exact hc1 (Subtype.ext h)
  have h3 : orderOf (c : Γ) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  exact ⟨c, c.2, h3, eq_zpowers_of_card_three_of_mem hY c.2 h3⟩

theorem map_eq_zpowers_of_isThreeCycle {Γ : Type*} [Group Γ] {n : ℕ} (e : Γ ≃* alternatingGroup (Fin n))
    {Y : Subgroup Γ} (hY : Nat.card Y = 3) {c : alternatingGroup (Fin n)}
    (hc3 : (c : Equiv.Perm (Fin n)).IsThreeCycle) (hc : c ∈ Y.map e.toMonoidHom) :
    Y.map e.toMonoidHom = Subgroup.zpowers c := by
  refine map_eq_zpowers_of_card_three_of_mem e hY hc ?_
  rw [← Subgroup.orderOf_coe c, hc3.orderOf]

end CFSG.HardMathSupport.RichardWeiss.Proving

end
