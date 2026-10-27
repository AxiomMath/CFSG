module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

section Heis

variable {F : Type} [Field F]

@[expose] def heisX : SL(3, F) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def heisY : SL(3, F) := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def heisZ : SL(3, F) := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_heisX :
    ((heisX : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem coe_heisY :
    ((heisY : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

theorem coe_heisZ :
    ((heisZ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := rfl

theorem heis_xy : (heisX : SL(3, F)) * heisY = heisZ * (heisY * heisX) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_heisX, coe_heisY, coe_heisZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem heis_zx : (heisZ : SL(3, F)) * heisX = heisX * heisZ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_heisX, coe_heisZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem heis_zy : (heisZ : SL(3, F)) * heisY = heisY * heisZ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_heisY, coe_heisZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem heis_z_ne_one : (heisZ : SL(3, F)) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp [coe_heisZ] at this

theorem heis_x_cube (h3 : (3 : F) = 0) : (heisX : SL(3, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [coe_heisX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem heis_y_cube (h3 : (3 : F) = 0) : (heisY : SL(3, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [coe_heisY]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem heis_comm : ⁅(heisX : SL(3, F)), (heisY : SL(3, F))⁆ = (heisZ : SL(3, F)) := by
  rw [commutatorElement_def, heis_xy (F := F)]
  group

theorem kl3_heis_of_hom (h3 : (3 : F) = 0) {G : Type} [Group G] (φ : SL(3, F) →* G)
    (hφ : Function.Injective φ) :
    ∃ x y : G, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ ⁅x, y⁆ * x = x * ⁅x, y⁆ ∧
      ⁅x, y⁆ * y = y * ⁅x, y⁆ := by
  refine ⟨φ heisX, φ heisY, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, heis_x_cube h3, map_one]
  · rw [← map_pow, heis_y_cube h3, map_one]
  · rw [← map_commutatorElement, heis_comm]
    intro h
    exact heis_z_ne_one (hφ (h.trans (map_one φ).symm))
  · rw [← map_commutatorElement, heis_comm, ← map_mul, ← map_mul, heis_zx]
  · rw [← map_commutatorElement, heis_comm, ← map_mul, ← map_mul, heis_zy]

end Heis

end CFSG.GH74.Generic.S1
