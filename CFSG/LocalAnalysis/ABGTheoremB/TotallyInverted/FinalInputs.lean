module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

@[expose] def ABG_II_4_4 (Δ : Data σ r) : Prop :=
  σ.DeltaEpsMinus ∧ r ∣ σ.q → ∀ Y : Subgroup G, Y ≤ σ.N → IsPGroup 2 Y →
    (Y ≤ Subgroup.centralizer (Δ.Q 0 : Set G) ∨ Y ≤ Subgroup.centralizer (Δ.Qs 0 : Set G)) →
      IsCyclic Y

@[expose] def ABG_II_4_10_iii (Δ : Data σ r) : Prop :=
  σ.DeltaEpsMinus ∧ r ∣ σ.q →
    ¬ (σ.C ⊓ Δ.J ≤ Subgroup.centralizer (Δ.Q 0 : Set G)) ∧
      ¬ (σ.C ⊓ Δ.J ≤ Subgroup.centralizer (Δ.Qs 0 : Set G))

@[expose] def ABG_II_4_18 (Δ : Data σ r) : Prop :=
  σ.DeltaEpsMinus ∧ r ∣ σ.q → ∀ Y Z : Subgroup G, Z ≤ Y →
    Y ≤ Subgroup.normalizer (Z : Set G) → Δ.J ≤ Subgroup.normalizer (Y : Set G) →
    Δ.J ≤ Subgroup.normalizer (Z : Set G) → (∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ Z) →
    (∀ y ∈ Y, y ^ r ∈ Z) → Nat.card Y = σ.q ^ 2 * Nat.card Z →
    (∀ j ∈ Δ.J, (∀ y ∈ Y, j * y * j⁻¹ * y⁻¹ ∈ Z) → j = 1) →
    ∀ Q ∈ ({Δ.Q 0, Δ.Qs 0} : Set (Subgroup G)),
      Nat.card {y : G | y ∈ Y ∧ ∀ u ∈ Q, u * y * u⁻¹ * y⁻¹ ∈ Z} ≤ σ.q * Nat.card Z

structure Inputs (Δ : Data σ r) : Prop where
  ii_4_4 : ABG_II_4_4 Δ
  ii_4_10_iii : ABG_II_4_10_iii Δ
  ii_4_18 : ABG_II_4_18 Δ

end CFSG.ABGTheoremB.TotallyInverted.Sec11
