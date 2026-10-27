module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.RankThree.Classical.SLnScalarCommutant

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem ker_slConjugation (n : ℕ) (K : Type) [Field K] :
    (slConjugation n K).ker = Subgroup.center (Matrix.GeneralLinearGroup (Fin n) K) := by
  ext A
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine _root_.CFSG.RankThree.Classical.mem_range_scalar_of_commute_elementary A
      fun i j hij => ?_
    let g : Matrix.SpecialLinearGroup (Fin n) K :=
      Matrix.SpecialLinearGroup.transvection hij 1
    have hg : (g : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j 1 :=
      Matrix.SpecialLinearGroup.transvection_coe hij 1
    have h1 : slConjugation n K A g = g := by
      simpa using DFunLike.congr_fun hA g
    have h2 : Matrix.SpecialLinearGroup.toGL g =
        A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ := by
      simpa [h1] using toGL_slConjugation n K A g
    have h3 : Matrix.SpecialLinearGroup.toGL g * A =
        A * Matrix.SpecialLinearGroup.toGL g := by
      conv_lhs => rw [h2]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have h4 : (Matrix.SpecialLinearGroup.toGL g : Matrix (Fin n) (Fin n) K) *
          (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) *
          (Matrix.SpecialLinearGroup.toGL g : Matrix (Fin n) (Fin n) K) := by
      simpa using congrArg Units.val h3
    simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hg] using h4
  · intro hA
    apply MulEquiv.ext
    intro g
    change slConjugation n K A g = g
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_slConjugation]
    have hcomm : A * Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL g * A :=
      (Subgroup.mem_center_iff.mp hA (Matrix.SpecialLinearGroup.toGL g)).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.LinearGroups
