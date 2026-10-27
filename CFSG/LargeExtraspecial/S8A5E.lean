module

public import CFSG.LargeExtraspecial.S8A5E0

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

structure PairData (M A N : Subgroup Γ) (t x : Γ) : Prop where
  hAM : A ≤ M
  hAN : A ≤ N
  hsq : ∀ a ∈ A, a * a = 1
  htA : t ∈ A
  ht1 : t ≠ 1
  hNc : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ zpowers t
  htN : ∀ n ∈ N, n * t = t * n
  hNorm : ∀ y ∈ M, y * t = t * y → ∀ n ∈ N, y * n * y⁻¹ ∈ N
  hP1 : ∀ y ∈ M, y * t * y⁻¹ * t = t * (y * t * y⁻¹) → y * t * y⁻¹ ≠ t →
    A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y A = ⊥
  hK : ∀ y ∈ M, y * t = t * y → ∀ a ∈ A ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y A,
    a ∉ zpowers t → CFSG.CGT.Timmesfeld75.conjSubgroup y A = A
  hxM : x ∈ M
  hσt : x * t * x⁻¹ * t = t * (x * t * x⁻¹)
  hσ1 : x * t * x⁻¹ ≠ t
  hF : ∀ a ∈ A, a ∈ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x A : Set Γ) ↔
    a * (x * t * x⁻¹) = x * t * x⁻¹ * a
  hF' : ∀ a ∈ A, a ∈ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ A : Set Γ) ↔
    a * (x⁻¹ * t * x⁻¹⁻¹) = x⁻¹ * t * x⁻¹⁻¹ * a
  h4 : 4 * Nat.card (A ⊓ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x A : Set Γ) :
    Subgroup Γ) ≤ Nat.card A
  h4' : 4 * Nat.card (A ⊓ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ A : Set Γ) :
    Subgroup Γ) ≤ Nat.card A
  h2 : 2 < Nat.card (A ⊓ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x A : Set Γ) :
    Subgroup Γ)
  h2' : 2 < Nat.card (A ⊓ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ A : Set Γ) :
    Subgroup Γ)

namespace PairData

variable {M A N : Subgroup Γ} {t x : Γ} (P : PairData M A N t x)
include P

omit P in
theorem comm_zpowers {z z' : Γ} (hz : z ∈ zpowers t) (hz' : z' ∈ zpowers t) :
    z * z' = z' * z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz'
  exact ((Commute.refl t).zpow_zpow k j).eq

omit P in
theorem F₁_eq : CFSG.CGT.Timmesfeld75.conjSubgroup x A ⊓ normalizer (A : Set Γ) =
    CFSG.CGT.Timmesfeld75.conjSubgroup x
      (A ⊓ normalizer (CFSG.CGT.Timmesfeld75.conjSubgroup x⁻¹ A : Set Γ)) := by
  ext b
  rw [conjSubgroup_inf, mem_inf, mem_inf]
  refine and_congr_right fun _ => ?_
  rw [mem_conjSubgroup]
  constructor
  · intro hb
    exact (mem_normalizer_conj_iff (g := x⁻¹)).mpr hb |> fun h => by
      simpa only [inv_inv] using h
  · intro hb
    have := (mem_normalizer_conj_iff (g := x⁻¹) (y := b)).mp (by simpa only [inv_inv] using hb)
    exact this

end PairData

end CFSG.LargeExtraspecial.S8
