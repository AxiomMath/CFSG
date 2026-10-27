module

public import CFSG.GH74.Uniqueness.Section15Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

structure Conf156 (M : Subgroup X) (n : ℕ) (L D K J Mo V R₁ : Subgroup X) (u : X) : Prop where
  F : Facts15 M n L D K J Mo V
  u_mem_J : u ∈ J
  u_sq : u * u = 1
  u_ne : u ≠ 1
  J_eq : ∀ j ∈ J, j = 1 ∨ j = u
  VD : ∀ d ∈ D, d ∈ V → d = 1 ∨ d = u
  C0_le : ∀ g ∈ M, (∀ x ∈ Mo, g * x = x * g) → g ∈ V
  NV : ∀ x ∈ V, x ∈ normalizer (L : Set X) → x ∈ Mo ∨ x * u ∈ Mo
  R₁_le : R₁ ≤ V
  Mo_le_R₁ : Mo ≤ R₁
  u_mem_R₁ : u ∈ R₁
  R₁_normal : ∀ g ∈ M, ∀ x ∈ R₁, g * x * g⁻¹ ∈ R₁
  card_R₁ : Nat.card R₁ = 2 ^ (2 * n + 1)
  sq_R₁ : ∀ x ∈ R₁, x * x ∈ Mo
  inv_R₁ : ∀ x ∈ R₁, x ∉ Mo → x * x = 1 → ∃ g ∈ M, g * u * g⁻¹ = x
  card_four : {x : X | x ∈ R₁ ∧ x * x ≠ 1}.ncard = 2 ^ n * (2 ^ n - 1)
  cent_K : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ R₁, k * x = x * k → x = 1 ∨ x = u
  big : R₁ ≠ V → Nat.card V = 2 ^ (3 * n + 1) ∧ (∀ g ∈ M, ∃ v ∈ V, ∃ d ∈ D, g = v * d) ∧
    (∀ k ∈ K, k ≠ 1 → ∀ x ∈ V, x⁻¹ * (k * x * k⁻¹) ∈ R₁ → x ∈ R₁)

end CFSG.GH74.Uniqueness
