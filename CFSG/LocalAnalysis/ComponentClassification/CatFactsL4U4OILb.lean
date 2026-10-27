module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k]

section Unipotent

variable (δ : k)

@[expose] def uE (t : extension δ) : SpecialLinearGroup (Fin 2) (extension δ) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lE (t : extension δ) : SpecialLinearGroup (Fin 2) (extension δ) :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem uE_mul (s t : extension δ) : uE δ s * uE δ t = uE δ (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [uE, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lE_mul (s t : extension δ) : lE δ s * lE δ t = lE δ (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [lE, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uE_zero : uE δ 0 = 1 := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [uE]

theorem lE_zero : lE δ 0 = 1 := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [lE]

theorem uE_pow (t : extension δ) (n : ℕ) : uE δ t ^ n = uE δ (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uE_zero]
  | succ n ih => rw [pow_succ, ih, uE_mul, Nat.cast_succ, add_mul, one_mul]

theorem lE_pow (t : extension δ) (n : ℕ) : lE δ t ^ n = lE δ (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, lE_zero]
  | succ n ih => rw [pow_succ, ih, lE_mul, Nat.cast_succ, add_mul, one_mul]

end Unipotent

section Coordinates

variable (δ : kˣ) (h2 : (2 : k) ≠ 0)

theorem coord_uE_one (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (uE (δ : k) 1) (hermitianCoordinates (δ : k) h2 x)) =
      ![x 0 + x 1 + 2 * x 2, x 1, x 2 + x 1, x 3] := by
  rw [hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val]
  have e : ((uE (δ : k) 1 : SpecialLinearGroup (Fin 2) (extension (δ : k))) :
      Matrix (Fin 2) (Fin 2) (extension (δ : k))) = !![1, 1; 0, 1] := rfl
  rw [e]
  funext i
  fin_cases i
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  all_goals ring

theorem coord_uE_omega (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (uE (δ : k) ⟨0, 1⟩) (hermitianCoordinates (δ : k) h2 x)) =
      ![x 0 - (δ : k) * x 1 - 2 * (δ : k) * x 3, x 1, x 2, x 3 + x 1] := by
  rw [hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val]
  have e : ((uE (δ : k) ⟨0, 1⟩ : SpecialLinearGroup (Fin 2) (extension (δ : k))) :
      Matrix (Fin 2) (Fin 2) (extension (δ : k))) = !![1, ⟨0, 1⟩; 0, 1] := rfl
  rw [e]
  funext i
  fin_cases i
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  all_goals ring

theorem coord_lE_one (x : Fin 4 → k) :
    (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ (lE (δ : k) 1) (hermitianCoordinates (δ : k) h2 x)) =
      ![x 0, x 1 + x 0 + 2 * x 2, x 2 + x 0, x 3] := by
  rw [hermitianCoordinates_symm_apply, rowOAction_val, hermitianCoordinates_val]
  have e : ((lE (δ : k) 1 : SpecialLinearGroup (Fin 2) (extension (δ : k))) :
      Matrix (Fin 2) (Fin 2) (extension (δ : k))) = !![1, 0; 1, 1] := rfl
  rw [e]
  funext i
  fin_cases i
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  all_goals ring

end Coordinates

end OIL

end CFSG.ComponentClassification.CatFactsL4U4
