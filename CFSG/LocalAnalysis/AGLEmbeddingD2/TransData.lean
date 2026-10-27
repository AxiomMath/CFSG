module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

section Data

variable {G : Type} [Group G] [Finite G]

structure D2TransData (p : ℕ) [Fact p.Prime] (M H R X A : Subgroup G) : Prop where
  pair : AGLPair p M H R
  le_A : X ≤ A
  A_le : A ≤ R
  card : Nat.card X = p
  A_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  A_exp : ∀ x ∈ A, x ^ p = 1
  trans : ∃ b ∈ R, (∀ x ∈ X, b * x * b⁻¹ = x) ∧ (∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ X) ∧
    ∃ a₀ ∈ A, ∀ k : ℕ, 0 < k → k < p → b ^ k * a₀ * (b ^ k)⁻¹ ≠ a₀
  inv : ∃ t ∈ H ⊓ M, ∃ e : ℕ, 6 ∣ e ∧ ∀ x ∈ X, t ^ e * x * (t ^ e)⁻¹ = x⁻¹
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H

end Data

end CFSG.AGLEmbeddingD2
