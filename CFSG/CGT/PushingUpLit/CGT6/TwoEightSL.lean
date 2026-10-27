module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

open CFSG.SL2MinimalFaithful Matrix

section SL

variable {F : Type*} [Field F]

@[expose] def lowerUnipotent (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_lowerUnipotent (t : F) :
    ((lowerUnipotent t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; t, 1] := rfl

@[expose] def diagSL (t : F) (ht : t ≠ 0) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![t, 0; 0, t⁻¹], by simp [Matrix.det_fin_two, ht]⟩

theorem coe_diagSL (t : F) (ht : t ≠ 0) :
    ((diagSL t ht : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![t, 0; 0, t⁻¹] := rfl

theorem diagSL_mul_unipotent (t : F) (ht : t ≠ 0) (x : F) :
    diagSL t ht * unipotent x = unipotent (t * t * x) * diagSL t ht := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem exists_sq_of_mul_unipotent (B : SpecialLinearGroup (Fin 2) F) (f : F → F)
    (h : ∀ x, B * unipotent x = unipotent (f x) * B) : ∃ b : F, b ≠ 0 ∧ ∀ x, f x = b * b * x := by
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ x i j, ((B * unipotent x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ((unipotent (f x) * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j :=
    fun x i j => by rw [h x]
  have e11 := e 1 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e11
  have hb3 : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e11
  have hb14 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [hb3, mul_zero, sub_zero] at hdet
    exact hdet
  refine ⟨(B : Matrix (Fin 2) (Fin 2) F) 0 0, left_ne_zero_of_mul_eq_one hb14, fun x => ?_⟩
  have e01 := e x 0 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e01
  have : f x * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = (B : Matrix (Fin 2) (Fin 2) F) 0 0 * x := by
    linear_combination -e01
  calc f x = f x * ((B : Matrix (Fin 2) (Fin 2) F) 1 1 * (B : Matrix (Fin 2) (Fin 2) F) 0 0) := by
        rw [mul_comm ((B : Matrix (Fin 2) (Fin 2) F) 1 1), hb14, mul_one]
    _ = (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (f x * (B : Matrix (Fin 2) (Fin 2) F) 1 1) := by ring
    _ = (B : Matrix (Fin 2) (Fin 2) F) 0 0 * ((B : Matrix (Fin 2) (Fin 2) F) 0 0 * x) := by
        rw [this]
    _ = (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 0 * x := by ring

end SL

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
