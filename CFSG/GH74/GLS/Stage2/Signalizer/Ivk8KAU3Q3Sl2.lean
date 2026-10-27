module

public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Sp
open scoped MatrixGroups commutatorElement

section Sl2Three

variable {k : Type} [Field k]

theorem u3q3_sl2Upper_pow_three (h3 : (3 : k) = 0) (c : k) : (sl2Upper c) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_succ, pow_one, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination c * h3

theorem u3q3_sl2Lower_pow_three (h3 : (3 : k) = 0) (c : k) : (sl2Lower c) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_succ, pow_one, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination c * h3

theorem sl2_closure_odd_of_three (h3 : (3 : k) = 0) :
    Subgroup.closure {A : SL(2, k) | Odd (orderOf A)} = ⊤ := by
  have hodd : ∀ A : SL(2, k), A ^ 3 = 1 → Odd (orderOf A) := fun A hA =>
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hA)
  rw [eq_top_iff]
  intro A _
  have hA := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A
  refine (Subgroup.closure_le _).2 ?_ hA
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Subgroup.subset_closure (hodd _ (u3q3_sl2Upper_pow_three h3 c))
  · exact Subgroup.subset_closure (hodd _ (u3q3_sl2Lower_pow_three h3 c))

theorem sl2_comm_sq (h3 : (3 : k) = 0) :
    ⁅(sl2Upper (1 : k)), (sl2Lower (1 : k))⁆ * ⁅(sl2Upper (1 : k)), (sl2Lower (1 : k))⁆ = -1 := by
  let c : SL(2, k) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hc : ((c : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![0, -1; 1, 0] := rfl
  have hmat : (sl2Upper (1 : k)) * (sl2Lower (1 : k)) =
      c * ((sl2Lower (1 : k)) * (sl2Upper (1 : k))) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hc, coe_sl2Upper, coe_sl2Lower]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h3
  have hcomm : ⁅(sl2Upper (1 : k)), (sl2Lower (1 : k))⁆ = c := by
    rw [commutatorElement_def, hmat]
    group
  rw [hcomm]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem u3q3_sl2_neg_one_ne_one (h2 : (2 : k) ≠ 0) : (-1 : SL(2, k)) ≠ 1 := by
  intro h
  have := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp at this
  apply h2
  linear_combination -this

end Sl2Three

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
