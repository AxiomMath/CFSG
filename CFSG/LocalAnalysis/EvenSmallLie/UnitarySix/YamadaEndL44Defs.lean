module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Matrix Subgroup CFSG.ClassicalInvolution.WeakCT CFSG.ABGLocalTools
open scoped MatrixGroups

section Defs

variable (F : Type) [Field F] [CharP F 2]

@[expose] def swapSL2 : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

@[expose] def sY (i : Fin 3) : SL(4, F) := blockSL2 F 3 i (swapSL2 F)

@[expose] def antiDiag : Matrix (Fin 4) (Fin 4) F := (Fin.revPerm : Equiv.Perm (Fin 4)).permMatrix F

omit [CharP F 2] in
theorem antiDiag_mul_self : antiDiag F * antiDiag F = 1 := by
  rw [antiDiag, ← Matrix.permMatrix_mul]
  have : (Fin.revPerm : Equiv.Perm (Fin 4)) * Fin.revPerm = 1 := by
    ext i
    simp
  rw [this, Matrix.permMatrix_one]

variable [Finite F]

@[expose] noncomputable def sigmaSL : SL(4, F) ≃* SL(4, F) :=
  (fieldAutSL (frobeniusEquiv F 2) 4).trans
    ((invTransposeSL 4).trans (conjSL (antiDiag F) (antiDiag F) (antiDiag_mul_self F)))

@[expose] noncomputable def msigma : Subgroup SL(4, F) :=
  MonoidHom.eqLocus (sigmaSL F).toMonoidHom (MonoidHom.id _)

end Defs

section Roots

variable (F : Type) [Field F]

@[expose] def rootSL (i j : Fin 4) : Subgroup SL(4, F) :=
  closure {A | ∃ (h : i ≠ j) (c : F), A = SpecialLinearGroup.transvection h c}

@[expose] def pstd : Subgroup SL(4, F) :=
  closure {A | ∃ (i j : Fin 4) (h : i ≠ j) (c : F), j < i ∧
    A = SpecialLinearGroup.transvection h c}

end Roots

@[expose] def L44Input : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
  ∀ (X : Type) [Group X] [Finite X] (L₁ : Subgroup X) (ψ : SL(4, F) →* L₁),
    Function.Surjective ψ → ψ.ker ≤ center SL(4, F) →
  ∀ t : X, t * t = 1 → t ∈ normalizer (L₁ : Set X) →
  ∀ χ : msigma F ≃* (L₁ ⊓ centralizer ({t} : Set X) : Subgroup X),
  ∀ P₁ : Subgroup X, IsSylowOf 2 P₁ L₁ →
    (∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ A : X) ∈ P₁) →
    ∃ φ : SL(4, F) →* X, Function.Injective φ ∧ φ.range = L₁ ∧
      (∀ A : msigma F, φ A = χ A) ∧ (∀ A, t * φ A * t⁻¹ = φ (sigmaSL F A)) ∧
      (pstd F).map φ = P₁

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
