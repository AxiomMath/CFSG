module

public import CFSG.ClassicalInvolution.Asc77.AscC5OStmt

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace C5O

section Statements

variable (p f : ℕ) [Fact p.Prime]


structure TwinShare {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    {M : Type} [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M) :
    Prop where
  data₁ : Om5Data p f Y₁ Φ₁ A₁ A₁' z₁ a₁ b₁
  data₂ : Om5Data p f Y₂ Φ₂ A₂ A₂' z₂ a₂ b₂
  range₁ : π₁.range = A₁ ⊔ A₁'
  range₂ : π₂.range = A₂ ⊔ A₂'
  odd₁ : Odd (Nat.card π₁.ker)
  odd₂ : Odd (Nat.card π₂.ker)
  map₁ : L.map π₁ = A₁ ∧ L'.map π₁ = A₁'
  map₂ : L.map π₂ = A₂ ∧ L'.map π₂ = A₂'
  swap : ∃ (τ : M → M) (τ₁ : Y₁ ≃* Y₁) (τ₂ : Y₂ ≃* Y₂),
    (∀ m ∈ L, τ m ∈ L') ∧ (∀ m ∈ L', τ m ∈ L) ∧
    (∀ m, π₁ (τ m) = τ₁ (π₁ m)) ∧ (∀ m, π₂ (τ m) = τ₂ (π₂ m)) ∧
    (∃ y : Y₂, ∀ x : Y₂, τ₂ x = y * x * y⁻¹) ∧ (∀ x : Y₁, τ₁ (τ₁ x) = x) ∧
    (∀ J ∈ Φ₁, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → τ₁ x ≠ x) ∧ ¬ HasBigFix p f τ₁

@[expose] def Om5TwinComm : Prop :=
  ∀ (Y₁ Y₂ : Type) [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    (M : Type) [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M),
    TwinShare p f Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L' →
    ∀ (γ₁ δ₁ : Y₁ ≃* Y₁) (γ₂ δ₂ : Y₂ ≃* Y₂),
      A₁.map γ₁.toMonoidHom = A₁ → A₁'.map γ₁.toMonoidHom = A₁' →
      A₂.map γ₂.toMonoidHom = A₂ → A₂'.map γ₂.toMonoidHom = A₂' →
      A₁.map δ₁.toMonoidHom = A₁ → A₁'.map δ₁.toMonoidHom = A₁' →
      A₂.map δ₂.toMonoidHom = A₂ → A₂'.map δ₂.toMonoidHom = A₂' →
      (∀ m : M, ∃ m' : M, π₁ m' = γ₁ (π₁ m) ∧ π₂ m' = γ₂ (π₂ m)) →
      (∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m)) →
        ∃ w : M, (∀ y : Y₁, γ₁ (δ₁ (γ₁.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
          ∀ y : Y₂, γ₂ (δ₂ (γ₂.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹

@[expose] def Om5TwinCommSwap : Prop :=
  ∀ (Y₁ Y₂ : Type) [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    (M : Type) [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M),
    TwinShare p f Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L' →
    ∀ (ψ : Y₁ ≃* Y₂) (ψ' : Y₂ ≃* Y₁) (δ₁ : Y₁ ≃* Y₁) (δ₂ : Y₂ ≃* Y₂),
      A₁.map ψ.toMonoidHom = A₂ → A₁'.map ψ.toMonoidHom = A₂' →
      A₂.map ψ'.toMonoidHom = A₁ → A₂'.map ψ'.toMonoidHom = A₁' →
      A₁.map δ₁.toMonoidHom = A₁ → A₁'.map δ₁.toMonoidHom = A₁' →
      A₂.map δ₂.toMonoidHom = A₂ → A₂'.map δ₂.toMonoidHom = A₂' →
      (∀ m : M, ∃ m' : M, π₂ m' = ψ (π₁ m) ∧ π₁ m' = ψ' (π₂ m)) →
      (∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m)) →
        ∃ w : M, (∀ y : Y₁, ψ' (δ₂ (ψ'.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
          ∀ y : Y₂, ψ (δ₁ (ψ.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹

structure M8GFacts : Prop where
  comm : Om5TwinComm p f
  commSwap : Om5TwinCommSwap p f

end Statements

end C5O

end CFSG.ClassicalInvolution.Asc77
