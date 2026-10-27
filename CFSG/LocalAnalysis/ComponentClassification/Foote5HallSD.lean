module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallGen

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}
  (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) (hk : 4 ∣ orderOf c)
include hD hk

theorem mul_mem_zpowers_of_refl {a b : G} (ha : a ∈ D) (hb : b ∈ D) (haC : a ∉ zpowers c)
    (hbC : b ∉ zpowers c) : a * b ∈ zpowers c := by
  have hac : a * c * a⁻¹ = c⁻¹ := by
    rcases hD a ha with h | ⟨-, h⟩
    · exact absurd h haC
    · exact h
  have hbc : b * c * b⁻¹ = c⁻¹ := by
    rcases hD b hb with h | ⟨-, h⟩
    · exact absurd h hbC
    · exact h
  rcases hD (a * b) (mul_mem ha hb) with h | ⟨-, h⟩
  · exact h
  · exfalso
    have h1 : (a * b) * c * (a * b)⁻¹ = c := by
      have h2 : a * c⁻¹ * a⁻¹ = c := by
        rw [show a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ by group, hac, inv_inv]
      calc (a * b) * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
        _ = c := by rw [hbc, h2]
    rw [h1] at h
    have h2 : c * c = 1 := by
      calc c * c = c * c⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [← h, mul_inv_cancel]
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := Nat.le_of_dvd (orderOf_pos c) hk
    omega

omit hD in
theorem sq_eq_or_eq_inv {p q : G} (hp : p ∈ zpowers c) (hq : q ∈ zpowers c)
    (hp2 : p * p = cz c) (hq2 : q * q = cz c) : p = q ∨ p = q⁻¹ := by
  have hcomm : Commute p q := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hq
    exact Commute.zpow_zpow_self c i j
  have hpq : p * q⁻¹ ∈ zpowers c := mul_mem hp (inv_mem hq)
  have hpq2 : (p * q⁻¹) * (p * q⁻¹) = 1 := by
    have h1 : (p * q⁻¹) * (p * q⁻¹) = (p * p) * (q * q)⁻¹ := by
      have hc' : q⁻¹ * p = p * q⁻¹ := (hcomm.inv_right).eq.symm
      calc (p * q⁻¹) * (p * q⁻¹) = p * (q⁻¹ * p) * q⁻¹ := by group
        _ = p * (p * q⁻¹) * q⁻¹ := by rw [hc']
        _ = (p * p) * (q * q)⁻¹ := by group
    rw [h1, hp2, hq2, mul_inv_cancel]
  rcases eq_one_or_eq_cz hk hpq hpq2 with h | h
  · left
    rw [mul_inv_eq_one] at h
    exact h
  · right
    have h1 : p = cz c * q := by rw [← h]; group
    rw [h1, ← hq2]
    have : q * q * q * q = 1 := by
      calc q * q * q * q = (q * q) * (q * q) := by group
        _ = 1 := by rw [hq2, cz_mul_cz hk]
    calc q * q * q = q * q * q * q * q⁻¹ := by group
      _ = q⁻¹ := by rw [this, one_mul]

theorem conj_not_mem_zpowers {x v : G} (hxN : x ∈ normalizer (D : Set G)) (hcD : c ∈ D)
    (hvC : v ∉ zpowers c) : x * v * x⁻¹ ∉ zpowers c := by
  intro h
  apply hvC
  have h1 : x⁻¹ * c * x⁻¹⁻¹ ∈ zpowers c := conj_c_mem hD hk (inv_mem hxN) hcD
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h
  have h2 : v = x⁻¹ * c ^ i * x⁻¹⁻¹ := by rw [hi, inv_inv]; group
  rw [h2, ← conj_zpow]
  exact zpow_mem h1 i

variable {x u : G} (hxN : x ∈ normalizer (D : Set G)) (hx2 : x * x = cz c)

variable (hxc : x * c * x⁻¹ = c⁻¹) (huD : u ∈ D) (huC : u ∉ zpowers c)
  (hxu : x * u * x⁻¹ * u ∉ zpowers (c ^ 2))
include hxN hx2 hxc huD huC hxu

end CFSG.ComponentClassification.Foote5.HallGen
