module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix QuadraticAlgebra
open scoped MatrixGroups

abbrev QE (F : Type) [Field F] : Type := QuadraticAlgebra F (-1 : F) 0

variable {F : Type} [Field F]

@[expose] def lm (z : QE F) : Matrix (Fin 2) (Fin 2) F := !![z.re, -z.im; z.im, z.re]

@[expose] def lmHom : QE F →+* Matrix (Fin 2) (Fin 2) F where
  toFun := lm
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lm]
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lm]
  map_add' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lm]
    ring

@[expose] def Phi : Matrix (Fin 2) (Fin 2) (QE F) →+* Matrix (Fin 4) (Fin 4) F :=
  (Matrix.reindexAlgEquiv F F (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)).toRingEquiv.toRingHom.comp
    ((Matrix.compRingEquiv (Fin 2) (Fin 2) F).toRingHom.comp lmHom.mapMatrix)

theorem Phi_apply (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    Phi N = !![(N 0 0).re, -(N 0 0).im, (N 0 1).re, -(N 0 1).im;
               (N 0 0).im, (N 0 0).re, (N 0 1).im, (N 0 1).re;
               (N 1 0).re, -(N 1 0).im, (N 1 1).re, -(N 1 1).im;
               (N 1 0).im, (N 1 0).re, (N 1 1).im, (N 1 1).re] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem Phi_injective : Function.Injective (Phi : Matrix (Fin 2) (Fin 2) (QE F) →+* _) := by
  intro N N' h
  rw [Phi_apply, Phi_apply] at h
  have e00 := congrFun (congrFun h 0) 0
  have e10 := congrFun (congrFun h 1) 0
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e30 := congrFun (congrFun h 3) 0
  have e22 := congrFun (congrFun h 2) 2
  have e32 := congrFun (congrFun h 3) 2
  simp at e00 e10 e02 e12 e20 e30 e22 e32
  have key : ∀ i j : Fin 2, (N i j).re = (N' i j).re ∧ (N i j).im = (N' i j).im := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨e00, e10⟩
    · exact ⟨e02, e12⟩
    · exact ⟨e20, e30⟩
    · exact ⟨e22, e32⟩
  exact Matrix.ext fun i j => QuadraticAlgebra.ext (key i j).1 (key i j).2

theorem det_Phi (N : Matrix (Fin 2) (Fin 2) (QE F)) : (Phi N).det = (N.det).norm := by
  rw [Phi_apply]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, QuadraticAlgebra.norm_def]
  ring

@[expose] def PhiSL : SL(2, QE F) →* SL(4, F) where
  toFun M := ⟨Phi M, by rw [det_Phi, M.2, QuadraticAlgebra.norm_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' M N := by
    apply Subtype.ext
    show Phi (((M * N : SL(2, QE F)) : Matrix (Fin 2) (Fin 2) (QE F))) =
      Phi (M : Matrix (Fin 2) (Fin 2) (QE F)) * Phi (N : Matrix (Fin 2) (Fin 2) (QE F))
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
