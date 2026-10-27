module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix
open scoped MatrixGroups

section Block

variable {F : Type} [Field F]

@[expose] def eFirst (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, A 0 0, A 0 1, A 0 2; 0, A 1 0, A 1 1, A 1 2; 0, A 2 0, A 2 1, A 2 2]

@[expose] def eLast (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, A 0 2, 0; A 1 0, A 1 1, A 1 2, 0; A 2 0, A 2 1, A 2 2, 0; 0, 0, 0, 1]

theorem eFirst_mul (A B : Matrix (Fin 3) (Fin 3) F) : eFirst (A * B) = eFirst A * eFirst B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eFirst, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem eFirst_one : eFirst (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eFirst]

theorem det_eFirst (A : Matrix (Fin 3) (Fin 3) F) : (eFirst A).det = A.det := by
  rw [Matrix.det_fin_three A]
  simp [eFirst, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem eLast_mul (A B : Matrix (Fin 3) (Fin 3) F) : eLast (A * B) = eLast A * eLast B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eLast, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem eLast_one : eLast (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eLast]

theorem det_eLast (A : Matrix (Fin 3) (Fin 3) F) : (eLast A).det = A.det := by
  rw [Matrix.det_fin_three A]
  simp [eLast, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def eFirstSL (A : SL(3, F)) : SL(4, F) :=
  ⟨eFirst (A : Matrix (Fin 3) (Fin 3) F), by rw [det_eFirst, A.2]⟩

@[expose] def eLastSL (A : SL(3, F)) : SL(4, F) :=
  ⟨eLast (A : Matrix (Fin 3) (Fin 3) F), by rw [det_eLast, A.2]⟩

theorem coe_eFirstSL (A : SL(3, F)) :
    ((eFirstSL A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = eFirst (A : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem coe_eLastSL (A : SL(3, F)) :
    ((eLastSL A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = eLast (A : Matrix (Fin 3) (Fin 3) F) :=
  rfl

@[expose] def eFirstHom : SL(3, F) →* SL(4, F) where
  toFun := eFirstSL
  map_one' := by
    apply Subtype.ext
    rw [coe_eFirstSL]
    exact eFirst_one
  map_mul' A B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_eFirstSL, coe_eFirstSL, coe_eFirstSL,
      Matrix.SpecialLinearGroup.coe_mul]
    exact eFirst_mul _ _

@[expose] def eLastHom : SL(3, F) →* SL(4, F) where
  toFun := eLastSL
  map_one' := by
    apply Subtype.ext
    rw [coe_eLastSL]
    exact eLast_one
  map_mul' A B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_eLastSL, coe_eLastSL, coe_eLastSL,
      Matrix.SpecialLinearGroup.coe_mul]
    exact eLast_mul _ _

theorem coe_eLastHom (A : SL(3, F)) :
    ((eLastHom A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = eLast (A : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem commute_eFirst {x : Matrix (Fin 4) (Fin 4) F} {H : Matrix (Fin 3) (Fin 3) F}
    (h : x * eFirst H = eFirst H * x) :
    (Matrix.of fun i j : Fin 3 => x i.succ j.succ) * H =
        H * (Matrix.of fun i j : Fin 3 => x i.succ j.succ) ∧
      H *ᵥ (fun i : Fin 3 => x i.succ 0) = (fun i : Fin 3 => x i.succ 0) ∧
      (fun j : Fin 3 => x 0 j.succ) ᵥ* H = (fun j : Fin 3 => x 0 j.succ) := by
  have hij : ∀ i j, (x * eFirst H) i j = (eFirst H * x) i j := fun i j => by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := hij i.succ j.succ
    fin_cases i <;> fin_cases j <;>
      simpa [eFirst, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four] using this
  · ext i
    have := hij i.succ 0
    fin_cases i <;>
      simpa [eFirst, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four] using this.symm
  · ext j
    have := hij 0 j.succ
    fin_cases j <;>
      simpa [eFirst, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four] using this

theorem commute_eLast {x : Matrix (Fin 4) (Fin 4) F} {H : Matrix (Fin 3) (Fin 3) F}
    (h : x * eLast H = eLast H * x) :
    (Matrix.of fun i j : Fin 3 => x i.castSucc j.castSucc) * H =
        H * (Matrix.of fun i j : Fin 3 => x i.castSucc j.castSucc) ∧
      H *ᵥ (fun i : Fin 3 => x i.castSucc 3) = (fun i : Fin 3 => x i.castSucc 3) ∧
      (fun j : Fin 3 => x 3 j.castSucc) ᵥ* H = (fun j : Fin 3 => x 3 j.castSucc) := by
  have hij : ∀ i j, (x * eLast H) i j = (eLast H * x) i j := fun i j => by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := hij i.castSucc j.castSucc
    fin_cases i <;> fin_cases j <;>
      simpa [eLast, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four] using this
  · ext i
    have := hij i.castSucc 3
    fin_cases i <;>
      simpa [eLast, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four] using this.symm
  · ext j
    have := hij 3 j.castSucc
    fin_cases j <;>
      simpa [eLast, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_four] using this

end Block

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
