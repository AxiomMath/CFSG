module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsUnitary

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K] (delta : K) [Fact (¬ IsSquare delta)]

@[expose] def sixGramSpecialUnitary : sixSpecialUnitary delta :=
  ⟨sixGramGL (extension delta), by
    constructor
    · change (sixBar delta (sixGram (extension delta))).transpose *
        sixGram (extension delta) * sixGram (extension delta) = sixGram (extension delta)
      rw [sixBar_gram, sixGram_transpose, sixGram_square, Matrix.one_mul]
    · exact sixGram_det (extension delta)⟩

theorem sixGramSpecialUnitary_action_ne_one (h2 : (2 : K) ≠ 0) :
    sixSpecialKappa delta h2 (sixGramSpecialUnitary delta) ≠ 1 := by
  intro h
  let X : sixSubmodule delta :=
    ⟨sixCoordinateMatrix delta ![1, 0, 0, 0, 0, 0],
      sixCoordinateMatrix_mem delta ![1, 0, 0, 0, 0, 0]⟩
  have hx := congrArg (fun g : SixIsometries delta => (g.val X).val 0 1) h
  rw [sixSpecialKappa_val] at hx
  change (sixGram (extension delta) * X.val * (sixGram (extension delta)).transpose) 0 1 =
    X.val 0 1 at hx
  simp [X, sixCoordinateMatrix, skewMatrix, sixGram, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ] at hx

theorem sixSpecialKappa_kernel_ne_top (h2 : (2 : K) ≠ 0) :
    (sixSpecialKappa delta h2).ker ≠ ⊤ := by
  intro h
  apply sixGramSpecialUnitary_action_ne_one delta h2
  exact (sixSpecialKappa delta h2).mem_ker.mp
    (h ▸ (show sixGramSpecialUnitary delta ∈ (⊤ : Subgroup (sixSpecialUnitary delta))
      from Subgroup.mem_top _))

variable [Finite K]

theorem sixSpecialKappa_range_quasisimple (h2 : (2 : K) ≠ 0) :
    CFSG.IsQuasisimple (sixSpecialKappa delta h2).range :=
  CatalogueBAlternating.quasisimple_iff_native.mpr
    (Quasisimple.range_quasisimple_of_ker_ne_top
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (sixSpecialUnitary_quasisimple delta h2))
      (sixSpecialKappa delta h2) (sixSpecialKappa_kernel_ne_top delta h2))

theorem sixSpecialKappa_range_pComponent_eq_top (h2 : (2 : K) ≠ 0)
    (p : ℕ) (L : Subgroup (sixSpecialKappa delta h2).range)
    (hL : CFSG.IsPComponent p L) : L = ⊤ :=
  CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple
    (sixSpecialKappa_range_quasisimple delta h2) p L hL

theorem sixSpecialKappa_range_pComponent_quasisimple (h2 : (2 : K) ≠ 0)
    (p : ℕ) (L : Subgroup (sixSpecialKappa delta h2).range)
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have htop := sixSpecialKappa_range_pComponent_eq_top delta h2 p L hL
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (sixSpecialKappa_range_quasisimple delta h2)))

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
