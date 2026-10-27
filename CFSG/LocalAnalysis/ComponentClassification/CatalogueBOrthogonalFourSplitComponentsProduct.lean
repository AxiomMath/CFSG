module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionProductQuasisimple

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents

universe u

variable {K : Type u} [Field K] [Finite K]

theorem specialLinearTwo_pComponent_quasisimple (p : ℕ) [Fact p.Prime]
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let N := CatalogueBGeneralLinear.specialLinearRange 2 K
  let e := CatalogueBGeneralLinear.specialLinearEquivRange 2 K
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hext := CatalogueBAlternating.pComponent_of_normal_subgroup p N
    (L.map e.toMonoidHom) hmap
  have hquasi := CatalogueBGeneralLinear.pComponent_quasisimple 2 K (by decide) p
    ((L.map e.toMonoidHom).map N.subtype) hext
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        ((L.map e.toMonoidHom).equivMapOfInjective N.subtype N.subtype_injective))
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem specialLinearTwo_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.generalLinear_two_small_solvable K (Or.inr hcard)
  exact Group.isSolvable_of_isSolvable_injective
    Matrix.SpecialLinearGroup.toGL_injective

theorem specialLinearProduct_pComponent_quasisimple (p : ℕ) [Fact p.Prime]
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolutionProduct.pComponent_quasisimple_product p
    (specialLinearTwo_pComponent_quasisimple p)
    (specialLinearTwo_pComponent_quasisimple p) L hL

theorem specialLinearProduct_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable
      (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    specialLinearTwo_three_solvable hcard
  infer_instance

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
