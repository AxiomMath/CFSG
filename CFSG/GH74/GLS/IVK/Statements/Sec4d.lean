module

public import CFSG.GH74.GLS.Stage4.T2Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest

@[expose] def IVK_4_7ab_G2 : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f → LieModel M .G2 0 p f →
    ∀ z : M, orderOf z = 2 →
      ∃ (K₁ K₂ : Subgroup M) (F : Type) (_ : Field F) (_ : Finite F) (t : M),
        Nat.card F = p ^ f ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧
        K₁ ⊓ K₂ = Subgroup.zpowers z ∧ Ch6Rem z K₁ K₂ F F t

@[expose] def IVK_4_7ab_D4 : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    LieModel M .trialityD4 0 p f → ∀ z : M, orderOf z = 2 →
      ∃ (K₁ K₂ : Subgroup M) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂)
        (t : M),
        Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧
        z ∈ K₁ ∧ z ∈ K₂ ∧ K₁ ⊓ K₂ = Subgroup.zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t

@[expose] def IVK_4_7ab : Prop := IVK_4_7ab_G2 ∧ IVK_4_7ab_D4

end CFSG.GH74.GLS.IVK
