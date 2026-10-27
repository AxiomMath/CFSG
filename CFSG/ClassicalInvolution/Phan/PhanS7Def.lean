module

public import CFSG.ClassicalInvolution.Phan.PhanH5Frames
public import CFSG.ClassicalInvolution.Phan.PhanS5Act
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def rotSL0 (a b : F) (h : a ^ 2 + b ^ 2 = 1) : SL(2, F) :=
  ⟨!![a, b; -b, a], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

@[expose] def rotSL1 (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1) : SL(2, F) :=
  ⟨!![a, b; -(4 * b), a], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

@[expose] noncomputable def La0 (h2 : (2 : F) ≠ 0) (A : SL(2, F)) : W7 F ≃ₗ[F] W7 F :=
  (fr0 h2).La A

@[expose] noncomputable def La1 (h2 : (2 : F) ≠ 0) (A : SL(2, F)) : W7 F ≃ₗ[F] W7 F :=
  (fr1 h2).La A

theorem rotSL0_apply (a b : F) (h : a ^ 2 + b ^ 2 = 1) :
    ((rotSL0 a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a] := rfl

theorem rotSL1_apply (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1) :
    ((rotSL1 a b h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; -(4 * b), a] := rfl

end CFSG.ClassicalInvolution.PhanB3.S
