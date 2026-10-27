module

public import CFSG.ClassicalInvolution.WeakCT.Sides

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem rotSL_mul_invTransposeSL_mul_inv (A : SL(2, K)) :
    rotSL * invTransposeSL 2 A * rotSL⁻¹ = A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rotSL_inv,
    coe_invTransposeSL]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [rotSL, CFSG.ClassicalInvolution.Phan.rotMat, CFSG.ClassicalInvolution.Phan.rotMatInv,
      Matrix.adjugate_fin_two]

@[expose] def blockSwapAut : SL(3, K) ≃* SL(3, K) :=
  (invTransposeSL 3).trans (MulAut.conj (swapSL : SL(3, K)))

theorem blockSwapAut_blk (s : Fin 2) (A : SL(2, K)) :
    blockSwapAut (blk K s A) = blk K s.rev A := by
  have h : ∀ B : SL(2, K), blockSwapAut (blk K s B) =
      swapSL * blk K s (invTransposeSL 2 B) * swapSL⁻¹ := by
    intro B
    fin_cases s
    · exact congrArg (fun g => swapSL * g * swapSL⁻¹)
        (invTransposeSL_blockSL (K := K) (m := 3) (k := 2) (i := 0) (by omega) B)
    · exact congrArg (fun g => swapSL * g * swapSL⁻¹)
        (invTransposeSL_blockSL (K := K) (m := 3) (k := 2) (i := 1) (by omega) B)
  rw [h, swap_blk, rotSL_mul_invTransposeSL_mul_inv]

theorem comp_blockSwapAut_blk {X : Type*} [Group X] (ψ : SL(3, K) →* X) (s : Fin 2) :
    (ψ.comp (blockSwapAut (K := K)).toMonoidHom).comp (blk K s) = ψ.comp (blk K s.rev) :=
  MonoidHom.ext fun A => congrArg ψ (blockSwapAut_blk s A)

end CFSG.ClassicalInvolution.Q3.Q3V
