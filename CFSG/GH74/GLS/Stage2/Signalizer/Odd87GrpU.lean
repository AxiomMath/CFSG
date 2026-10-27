module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section Z

variable {B : Type} [Group B]

theorem sq_eq_one_of_inverted_normalizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K X : Subgroup B} (hXp : IsPGroup p ↥X) {z : B}
    (hzX : z ∈ normalizer (X : Set B))
    (hC : ∀ c ∈ K, c * z = z * c → c ∈ normalizer (X : Set B))
    (hN : K ⊓ normalizer (X : Set B) ≤ X ⊔ K ⊓ centralizer ({z} : Set B))
    {y : B} (hyK : y ∈ K) (hyN : y ∈ normalizer (X : Set B)) (hyz : z * y * z⁻¹ = y⁻¹)
    (hy4 : (y * y) * (y * y) = 1) : y * y = 1 := by
  have hD : K ⊓ centralizer ({z} : Set B) ≤ normalizer (X : Set B) := fun c ⟨hcK, hcC⟩ =>
    hC c hcK (Subgroup.mem_centralizer_iff.mp hcC z (Set.mem_singleton z)).symm
  have hy : y ∈ ((X ⊔ K ⊓ centralizer ({z} : Set B) : Subgroup B) : Set B) := hN ⟨hyK, hyN⟩
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X _ hD] at hy
  obtain ⟨x, hx, c, ⟨hcK, hcC⟩, rfl⟩ := hy
  have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hcC z (Set.mem_singleton z)).symm
  have hz_inv : z * x⁻¹ * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hzX x⁻¹).mp (X.inv_mem hx)
  have hsq : (x * c) * (x * c) = x * (z * x⁻¹ * z⁻¹) := by
    have h1 : z * (x * c) * z⁻¹ = (x * c)⁻¹ := hyz
    calc (x * c) * (x * c) = (x * c) * ((x * c)⁻¹)⁻¹ := by rw [inv_inv]
      _ = (x * c) * (z * (x * c) * z⁻¹)⁻¹ := by rw [h1]
      _ = x * (c * z * c⁻¹) * x⁻¹ * z⁻¹ := by group
      _ = x * z * x⁻¹ * z⁻¹ := by rw [hcz]; group
      _ = x * (z * x⁻¹ * z⁻¹) := by group
  have hX2 : (x * c) * (x * c) ∈ X := hsq ▸ X.mul_mem hx hz_inv
  obtain ⟨k, hk⟩ := hXp ⟨(x * c) * (x * c), hX2⟩
  have hk' : ((x * c) * (x * c)) ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (p ^ k) := by
    exact (Nat.Prime.odd_of_ne_two hp hp2).pow
  set w := (x * c) * (x * c) with hw
  have hw2 : w * w = 1 := hy4
  obtain ⟨t, ht⟩ := hodd
  calc w = w ^ (2 * t + 1) := by
        rw [pow_succ, pow_mul, show w ^ 2 = 1 by rw [pow_two]; exact hw2, one_pow, one_mul]
    _ = 1 := by rw [ht] at hk'; exact hk'

end Z

section ZMem

variable {A : Type} [Group A] [Finite A]

theorem mem_of_mem_sup_centralizer {J : Subgroup A} {z : A} (hz2 : z * z = 1)
    (hz : z ∈ J ⊔ centralizer (J : Set A))
    (hf : ∀ c : A, orderOf c = 2 → c ∈ centralizer (J : Set A) → False) : z ∈ J := by
  have hC : centralizer (J : Set A) ≤ normalizer (J : Set A) := Subgroup.centralizer_le_normalizer (J : Set A)
  have hz' : z ∈ ((J ⊔ centralizer (J : Set A) : Subgroup A) : Set A) := hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left J _ hC] at hz'
  obtain ⟨s, hs, c, hc, rfl⟩ := hz'
  have hsc : s * c = c * s := (Subgroup.mem_centralizer_iff.mp hc s hs)
  have hz2' : (s * s) * (c * c) = 1 := by
    calc (s * s) * (c * c) = s * (s * c) * c := by group
      _ = s * (c * s) * c := by rw [hsc]
      _ = s * c * (s * c) := by group
      _ = 1 := hz2
  have hcc : c * c ∈ J := by
    have := eq_inv_of_mul_eq_one_right hz2'
    rw [this]
    exact J.inv_mem (J.mul_mem hs hs)
  have hodd : Odd (orderOf c) := by
    by_contra hne
    have heven : Even (orderOf c) := Nat.not_odd_iff_even.mp hne
    obtain ⟨m, hm⟩ := heven
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := orderOf_pos c
      omega
    have hord : orderOf (c ^ m) = 2 := by
      have h2m : orderOf c = 2 * m := by omega
      rw [orderOf_pow_of_dvd hm0 ⟨2, by omega⟩, h2m, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    exact hf (c ^ m) hord (Subgroup.pow_mem _ hc m)
  obtain ⟨m, hm⟩ := hodd
  have hcJ : c ∈ J := by
    have h1 : c = (c * c) ^ (m + 1) := by
      have : c ^ (orderOf c) = 1 := pow_orderOf_eq_one c
      calc c = c * c ^ (orderOf c) := by rw [this, mul_one]
        _ = c ^ (2 * m + 1 + 1) := by rw [← hm]; group
        _ = (c * c) ^ (m + 1) := by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, pow_two]
    rw [h1]
    exact J.pow_mem hcc _
  exact J.mul_mem hs hcJ

end ZMem

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
