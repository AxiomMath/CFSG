module

import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.OrderOfElement

open MulAction Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a : ℕ} {P : Type*} [Group P]

private theorem finite_of_natCard_eq_pow {Q : Type*} (hp : p.Prime) (hQ : Nat.card Q = p ^ a) :
    Finite Q :=
  Nat.finite_of_card_ne_zero (by rw [hQ]; exact pow_ne_zero _ hp.pos.ne')

theorem dvd_natCard_center (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    p ∣ Nat.card (center P) := by
  have := Fact.mk hp
  have : Finite P := finite_of_natCard_eq_pow hp hP
  have hcard : Nat.card (ConjAct P) = p ^ a := hP
  have hmod := natCard_modEq_natCard_fixedPoints (P := ConjAct P) (X := P) hcard
  have hdvd : p ∣ Nat.card P := hP ▸ dvd_pow_self p (Nat.one_le_iff_ne_zero.mp ha)
  have h := Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  rwa [ConjAct.fixedPoints_eq_center] at h

theorem exists_mem_center_orderOf_eq (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    ∃ z : P, z ∈ center P ∧ orderOf z = p := by
  have := Fact.mk hp
  have : Finite P := finite_of_natCard_eq_pow hp hP
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := center P) p (dvd_natCard_center hp hP ha)
  exact ⟨z, z.2, by rwa [Subgroup.orderOf_coe]⟩

theorem center_nontrivial (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    Nontrivial (center P) := by
  obtain ⟨z, hzc, hz⟩ := exists_mem_center_orderOf_eq hp hP ha
  have hz1 : z ≠ 1 := fun h => hp.one_lt.ne (by rw [← hz, h, orderOf_one])
  exact ⟨⟨⟨z, hzc⟩, 1, by simpa using hz1⟩⟩

theorem center_ne_bot (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    center P ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot _).mp (center_nontrivial hp hP ha)

theorem exists_natCard_center_eq_pow (hp : p.Prime) (hP : Nat.card P = p ^ a) (ha : 1 ≤ a) :
    ∃ k, 0 < k ∧ Nat.card (center P) = p ^ k := by
  have := Fact.mk hp
  have : Finite P := finite_of_natCard_eq_pow hp hP
  obtain ⟨k, hk, hcard⟩ :=
    IsPGroup.card_center_eq_prime_pow (p := p) (n := a) hP (Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
  exact ⟨k, hk, hcard⟩

end

end CFSG.FeitThompson
