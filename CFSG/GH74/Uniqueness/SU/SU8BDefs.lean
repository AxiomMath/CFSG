module

public import CFSG.GH74.Uniqueness.SU.SU8Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup

variable {G : Type} [Group G]

structure CaseB (L A V₀ : Subgroup G) (z : G) : Prop where
  A_exp : ∀ a ∈ A, a * a = 1
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  V₀_le : V₀ ≤ A
  z_mem : z ∈ V₀
  z_ne : z ≠ 1
  card_A : Nat.card A = 8 * Nat.card V₀
  act_C : ∀ g ∈ L ⊓ normalizer (A : Set G), ∀ c ∈ V₀, g * c * g⁻¹ = c
  inf_gt : 1 < Nat.card ↥(V₀ ⊓ L)
  inf_le : Nat.card ↥(V₀ ⊓ L) ≤ 4
  gen : ∃ g₀ ∈ L ⊓ normalizer (A : Set G), (∃ e : ℕ, g₀ ^ (7 ^ e) = 1) ∧
    (∀ a ∈ A, g₀ ^ 7 * a * (g₀ ^ 7)⁻¹ = a) ∧
    (∀ a ∈ A, a ∉ V₀ → ∀ j : ℕ, 0 < j → j < 7 → g₀ ^ j * a * (g₀ ^ j)⁻¹ * a⁻¹ ∉ V₀) ∧
    (∀ a ∈ A, a ∉ V₀ → ∀ b ∈ A, b ∉ V₀ → ∃ j : ℕ, g₀ ^ j * a * (g₀ ^ j)⁻¹ * b⁻¹ ∈ V₀) ∧
    (∀ m ∈ L ⊓ normalizer (A : Set G), ∃ j : ℕ,
      ∀ a ∈ A, m * a * m⁻¹ * (g₀ ^ j * a * (g₀ ^ j)⁻¹)⁻¹ ∈ V₀)
  two_elt : Nat.card V₀ = 2 → ∃ t ∈ L ⊓ normalizer (A : Set G), (∃ k : ℕ, t ^ (2 ^ k) = 1) ∧
    ∃ a ∈ A, t * a * t⁻¹ ≠ a
  cent : Nat.card V₀ = 2 → ∀ g ∈ normalizer (A : Set G), g * z = z * g →
    ∃ m ∈ L ⊓ normalizer (A : Set G), ∀ a ∈ A, g * a * g⁻¹ = m * a * m⁻¹

end CFSG.GH74.Uniqueness.SU.SU8
