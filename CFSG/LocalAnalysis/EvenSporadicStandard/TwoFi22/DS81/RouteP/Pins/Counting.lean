module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem card_subgroupOf_eq_card_inf {G : Type*} [Group G] (N L : Subgroup G) :
    Nat.card ↥(L.subgroupOf N) = Nat.card ↥(N ⊓ L) := by
  rw [← Subgroup.inf_subgroupOf_left L N]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem eq_of_le_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {A B H : Subgroup G}
    (hAB : A ≤ B) (hBH : B ≤ H) (hne : ∃ x ∈ H, x ∉ B)
    (hcard : Nat.card ↥H = 2 * Nat.card ↥A) : A = B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hAB
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hdvd : Nat.card ↥A * k ∣ 2 * Nat.card ↥A := by
    rw [← hk, ← hcard]
    exact Subgroup.card_dvd_of_le hBH
  have hk_dvd : k ∣ 2 := by
    rw [mul_comm 2 (Nat.card ↥A)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hApos).mp hdvd
  have hk_le : k ≤ 2 := Nat.le_of_dvd (by omega) hk_dvd
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    have hzero : Nat.card ↥B = 0 := by rw [hk, hk0, mul_zero]
    omega
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · apply Subgroup.eq_of_le_of_card_ge hAB
    rw [hk]
    simp
  · exfalso
    have hBH_eq : B = H := by
      apply Subgroup.eq_of_le_of_card_ge hBH
      rw [hcard, hk, mul_comm (Nat.card ↥A) 2]
    obtain ⟨x, hxH, hxB⟩ := hne
    rw [← hBH_eq] at hxH
    exact hxB hxH

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
