module

public import CFSG.ClassicalInvolution.Asc77.AscC25X1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

namespace C5O

section Statements

variable (p f : ℕ) [Fact p.Prime]


structure Om5Data (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y)
    (z' a₀ b₀ : Y) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  lie : ∃ D : LieSystemData p f Y Φ, D.card = 1 ∧
    ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)
  twin : TwinSect0 Φ A A' z' a₀ b₀
  conj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ

@[expose] def HasBigFix {Y : Type} [Group Y] (β : Y ≃* Y) : Prop :=
  ∃ L : Subgroup Y, (∀ x ∈ L, β x = x) ∧ IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
    Nat.card (SL(2, GaloisField p f)) ^ 2 < 4 * Nat.card L

@[expose] def Om5Centerless : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1

@[expose] def Om5InvFixFour : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ y : Y, y * y = 1 → y ≠ 1 →
      ∃ J ∈ Φ, ∃ x ∈ J, x * x * x * x = 1 ∧ x * x ≠ 1 ∧ y * x = x * y

@[expose] def Om5InnerOfTwin : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ β : Y ≃* Y, A.map β.toMonoidHom = A →
      A'.map β.toMonoidHom = A' → (∃ g ∈ A, ∀ x ∈ A, β x = g * x * g⁻¹) →
        ∃ y : Y, ∀ x : Y, β x = y * x * y⁻¹

@[expose] def Om5TwinOfInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ y : Y, conjSub y A = A →
      ∃ g ∈ A, ∀ x ∈ A, y * x * y⁻¹ = g * x * g⁻¹

@[expose] def Om5Interchange : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ (β : Y ≃* Y) (t' : Y), t' = β z' → t' ≠ z' →
      t' * z' = z' * t' →
        (∃ x : Y, x * z' * x⁻¹ = t' ∧ x * t' * x⁻¹ = z') ∧
          ∃ x : Y, x * (z' * t') * x⁻¹ = a₀ * b₀

@[expose] def Om5ZSwap : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ →
      ∃ s : Y, s * s = 1 ∧ conjSub s A = A' ∧ ∃ x : Y, x * z' * x⁻¹ = s

@[expose] def Om5USwapNotZ : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ s : Y, conjSub s A = A' → (∃ x : Y, x * z' * x⁻¹ = s) →
      ∀ β : Y ≃* Y, β z' ≠ s * z'

@[expose] def Om5ExcClass : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data p f Y Φ A A' z' a₀ b₀ → ∀ β₁ β₂ : Y ≃* Y,
      (∀ x : Y, β₁ (β₁ x) = x) → (∀ x : Y, β₂ (β₂ x) = x) →
      (∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₁ x ≠ x) →
      (∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₂ x ≠ x) →
      ¬ HasBigFix p f β₁ → ¬ HasBigFix p f β₂ →
        ∃ g : Y, ∀ x : Y, β₂ x = g * β₁ (g⁻¹ * x * g) * g⁻¹

@[expose] def SL2PerfectAut : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ P : Subgroup (MulAut (SL(2, GaloisField p f))), ⁅P, P⁆ = P →
    2 * Nat.card P ≤ Nat.card (SL(2, GaloisField p f))

structure ModelFacts : Prop where
  invFixFour : Om5InvFixFour p f
  innerOfTwin : Om5InnerOfTwin p f
  twinOfInner : Om5TwinOfInner p f
  interchange : Om5Interchange p f
  zSwap : Om5ZSwap p f
  uSwapNotZ : Om5USwapNotZ p f
  excClass : Om5ExcClass p f
  centerless : Om5Centerless p f
  sl2PerfectAut : SL2PerfectAut p f

end Statements

end C5O

end CFSG.ClassicalInvolution.Asc77
