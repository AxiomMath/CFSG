module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
public import CFSG.HardMathSupport.Timmesfeld.Torality.A4Block

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
namespace KSE8Five
namespace One

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
open CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups Fin.NatCast

variable {K : Type} [Field K]

theorem cycMat5_apply (a : Fin 5 → K) (j k : Fin 5) :
    cycMat5 a j k = if j = k + 1 then a k else 0 := by
  fin_cases j <;> fin_cases k <;> simp [cycMat5]

theorem coe_rotSL_eq_cycMat5 :
    ((rotSL : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = cycMat5 (fun _ => 1) := by
  rw [coe_rotSL]
  ext i j
  rw [cycMat5_apply]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def,
    finRotate_succ_symm_apply, sub_eq_iff_eq_add]

theorem diagonal_mul_cycMat5 (d a : Fin 5 → K) :
    Matrix.diagonal d * cycMat5 a = cycMat5 (fun j => d (j + 1) * a j) := by
  ext i j
  by_cases h : i = j + 1 <;> simp [cycMat5_apply, Matrix.diagonal_mul, h]

theorem coe_rotSL_pow_nat (n : ℕ) :
    (((rotSL : SL(5, K)) ^ n : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.of (fun l k : Fin 5 => if l = k + (n : Fin 5) then (1 : K) else 0) := by
  induction n with
  | zero => ext l k; simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_rotSL_eq_cycMat5]
    ext l k
    have e : k + ((n + 1 : ℕ) : Fin 5) = k + 1 + (n : Fin 5) := by
      rw [Nat.cast_succ, add_comm (n : Fin 5) 1, ← add_assoc]
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, cycMat5_apply]
    rw [e]
    simp [mul_ite, Finset.sum_ite_eq']

theorem coe_rotSL_pow (s : Fin 5) :
    (((rotSL : SL(5, K)) ^ (s : ℕ) : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.of (fun l k : Fin 5 => if l = k + s then (1 : K) else 0) := by
  rw [coe_rotSL_pow_nat, Fin.cast_val_eq_self]

theorem prod_sgn_eq_one :
    ∏ i : Fin 5, (((if i = 4 then (1 : Kˣ) else -1 : Kˣ)) : K) = 1 := by
  simp [Fin.prod_univ_five]

theorem coxSL5_eq_rotSL_mul :
    (coxSL5 : SL(5, K)) =
      rotSL * diagSLn (fun i : Fin 5 => if i = 4 then (1 : Kˣ) else -1) prod_sgn_eq_one := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_coxSL5, coe_rotSL_eq_cycMat5, coe_diagSLn,
    cycMat5_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> simp

theorem coxSL5_pow_five : (coxSL5 : SL(5, K)) ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_coxSL5, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, cycMat5, Matrix.mul_apply, Fin.sum_univ_five]

end One
end KSE8Five
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
