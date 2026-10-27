module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem iotaTwo_elem01 (s : K) :
    plusIotaTwo K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) s) =
      rpElt (Sum.inl 0) (Sum.inl 1) s := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [rpElt_apply (by simp)]
  fin_cases c <;>
  simp [plusIotaTwo_apply_inl, plusIotaTwo_apply_inr, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply] <;> ring

theorem iotaTwo_elem10 (s : K) :
    plusIotaTwo K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) s) =
      rpElt (Sum.inl 1) (Sum.inl 0) s := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [rpElt_apply (by simp)]
  fin_cases c <;>
  simp [plusIotaTwo_apply_inl, plusIotaTwo_apply_inr, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply] <;> ring

theorem iotaOne_elem01 (s : K) :
    plusIotaOne K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) s) =
      rpElt (Sum.inl 0) (Sum.inr 1) s := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [rpElt_apply (by simp), plusIotaOne_apply]
  fin_cases c <;>
  simp [LinearEquiv.mul_apply, swapPair_apply, Equiv.swap_apply_def, plusIotaTwo_apply_inl,
    plusIotaTwo_apply_inr, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply] <;> ring

theorem iotaOne_elem10 (s : K) :
    plusIotaOne K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) s) =
      rpElt (Sum.inr 1) (Sum.inl 0) s := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [rpElt_apply (by simp), plusIotaOne_apply]
  fin_cases c <;>
  simp [LinearEquiv.mul_apply, swapPair_apply, Equiv.swap_apply_def, plusIotaTwo_apply_inl,
    plusIotaTwo_apply_inr, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.single_apply, Pi.single_apply] <;> ring


theorem rpElt_two_cases {a b : Fin 2 ⊕ Fin 2} (hab : coordIdx a ≠ coordIdx b) (s : K) :
    (∃ A : SL(2, K), rpElt a b s = plusIotaTwo K A) ∨
      ∃ A : SL(2, K), rpElt a b s = plusIotaOne K A := by
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hab
    | exact Or.inl ⟨_, (iotaTwo_elem01 s).symm⟩
    | exact Or.inl ⟨_, (iotaTwo_elem10 s).symm⟩
    | exact Or.inr ⟨_, (iotaOne_elem01 s).symm⟩
    | exact Or.inr ⟨_, (iotaOne_elem10 s).symm⟩
    | exact Or.inl ⟨_, (rpElt_swap_swap (a := Sum.inl 0) (b := Sum.inl 1) (by simp) s).trans
        (iotaTwo_elem01 (-s)).symm⟩
    | exact Or.inl ⟨_, (rpElt_swap_swap (a := Sum.inl 1) (b := Sum.inl 0) (by simp) s).trans
        (iotaTwo_elem10 (-s)).symm⟩
    | exact Or.inr ⟨_, (rpElt_swap_swap (a := Sum.inl 0) (b := Sum.inr 1) (by simp) s).trans
        (iotaOne_elem01 (-s)).symm⟩
    | exact Or.inr ⟨_, (rpElt_swap_swap (a := Sum.inr 1) (b := Sum.inl 0) (by simp) s).trans
        (iotaOne_elem10 (-s)).symm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
