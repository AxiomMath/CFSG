module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpTens
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem transpose_J0_mul (h : SL(2, F)) :
    (h : Matrix (Fin 2) (Fin 2) F)ᵀ * J0 * (h : Matrix (Fin 2) (Fin 2) F) = J0 := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) F).det = 1 := h.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J0, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination hdet | linear_combination (-1 : F) * hdet

theorem tens_symplectic (h : SL(2, F)) :
    (tens (h : Matrix (Fin 2) (Fin 2) F) 1)ᵀ * gram F 2 * tens (h : Matrix (Fin 2) (Fin 2) F) 1 =
      gram F 2 := by
  rw [gram_eq_tens, tens_transpose, tens_mul, tens_mul, transpose_J0_mul]
  simp

@[expose] noncomputable def diagSL (h : SL(2, F)) : StatedSp 2 F :=
  ofSymplecticMat (tens (h : Matrix (Fin 2) (Fin 2) F) 1) (tens_symplectic h)

theorem mat_diagSL (h : SL(2, F)) : mat 2 F (diagSL h) = tens (h : Matrix (Fin 2) (Fin 2) F) 1 :=
  rfl

theorem diagSL_mul (h h' : SL(2, F)) : diagSL (h * h') = diagSL h * diagSL h' := by
  refine mat_injective ?_
  rw [map_mul, mat_diagSL, mat_diagSL, mat_diagSL, tens_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp

theorem diagSL_one : diagSL (1 : SL(2, F)) = 1 := by
  refine mat_injective ?_
  rw [mat_diagSL, map_one]
  simpa using tens_one_one

@[expose] noncomputable def Δsl : SL(2, F) →* StatedSp 2 F where
  toFun := diagSL
  map_one' := diagSL_one
  map_mul' := diagSL_mul

theorem Δsl_apply (h : SL(2, F)) : Δsl h = diagSL h := rfl

theorem mat_Δsl (h : SL(2, F)) : mat 2 F (Δsl h) = tens (h : Matrix (Fin 2) (Fin 2) F) 1 := rfl

theorem Δsl_injective : Function.Injective (Δsl : SL(2, F) →* StatedSp 2 F) := by
  intro h h' e
  have := congrArg (mat 2 F) e
  rw [mat_Δsl, mat_Δsl] at this
  have e00 := congrFun (congrFun this (Sum.inl 0)) (Sum.inl 0)
  have e01 := congrFun (congrFun this (Sum.inl 0)) (Sum.inr 0)
  have e10 := congrFun (congrFun this (Sum.inr 0)) (Sum.inl 0)
  have e11 := congrFun (congrFun this (Sum.inr 0)) (Sum.inr 0)
  simp [tens] at e00 e01 e10 e11
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simpa

theorem Δsl_commute_xSw (h : SL(2, F)) : Δsl h * xSw = xSw * Δsl h := by
  refine mat_injective ?_
  rw [map_mul, map_mul, mat_Δsl, mat_xSw, tens_mul, tens_mul]
  simp

theorem isQuasisimple_range_Δsl [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple (Δsl (F := F)).range :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (MonoidHom.ofInjective Δsl_injective).symm
    (CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.isQuasisimple_SL_of_two_le le_rfl h4)

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
