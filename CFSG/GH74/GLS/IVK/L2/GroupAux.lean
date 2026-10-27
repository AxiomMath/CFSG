module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup

theorem mem_sup_zpowers_iff {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (P : Set G)) {x : G} :
    x ∈ P ⊔ zpowers g ↔ ∃ p ∈ P, ∃ k : ℤ, x = p * g ^ k := by
  have hk : ∀ (k : ℤ) (p : G), p ∈ P → g ^ k * p * (g ^ k)⁻¹ ∈ P := by
    intro k p hp
    have hkmem : g ^ k ∈ normalizer (P : Set G) := Subgroup.zpow_mem _ hg k
    exact (Subgroup.mem_normalizer_iff.mp hkmem p).mp hp
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ p ∈ P, ∃ k : ℤ, x = p * g ^ k}
        one_mem' := ⟨1, P.one_mem, 0, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨p₁, hp₁, k₁, rfl⟩ ⟨p₂, hp₂, k₂, rfl⟩
          refine ⟨p₁ * (g ^ k₁ * p₂ * (g ^ k₁)⁻¹), P.mul_mem hp₁ (hk k₁ p₂ hp₂), k₁ + k₂, ?_⟩
          rw [zpow_add]; group
        inv_mem' := by
          rintro _ ⟨p, hp, k, rfl⟩
          refine ⟨g ^ (-k) * p⁻¹ * (g ^ (-k))⁻¹, hk (-k) p⁻¹ (P.inv_mem hp), -k, ?_⟩
          group }
    have hle : P ⊔ zpowers g ≤ S :=
      sup_le (fun p hp => ⟨p, hp, 0, by simp⟩) (zpowers_le.mpr ⟨1, P.one_mem, 1, by simp⟩)
    exact hle hx
  · rintro ⟨p, hp, k, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (mem_zpowers g) k))

theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
          refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
          have := hc h₂ hh₂ k₁ hk₁
          calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
            _ = h₁ * (h₂ * k₁) * k₂ := by rw [this]
            _ = h₁ * h₂ * (k₁ * k₂) := by group
        inv_mem' := by
          rintro _ ⟨h, hh, k, hk, rfl⟩
          refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
          exact Commute.mul_inv (hc h hh k hk) }
    have hle : H ⊔ K ≤ S :=
      sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
        (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
    exact hle hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

theorem isPGroup_sup_of_commute {G : Type*} [Group G] {p : ℕ} {H K : Subgroup G}
    (hH : IsPGroup p ↥H) (hK : IsPGroup p ↥K) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    IsPGroup p ↥(H ⊔ K) := by
  intro x
  obtain ⟨h, hh, k, hk, hx⟩ := (mem_sup_of_commute hc).mp x.2
  obtain ⟨i, hi⟩ := hH ⟨h, hh⟩
  obtain ⟨j, hj⟩ := hK ⟨k, hk⟩
  have hi' : h ^ (p ^ i) = 1 := congrArg Subtype.val hi
  have hj' : k ^ (p ^ j) = 1 := congrArg Subtype.val hj
  refine ⟨i + j, ?_⟩
  apply Subtype.ext
  have hxv : (x : G) = h * k := hx
  have hcomm : Commute h k := hc h hh k hk
  show (x : G) ^ (p ^ (i + j)) = 1
  rw [hxv, hcomm.mul_pow, pow_add, pow_mul, hi', one_pow, mul_comm (p ^ i), pow_mul, hj',
    one_pow, one_mul]

end CFSG.GH74.GLS.IVK
