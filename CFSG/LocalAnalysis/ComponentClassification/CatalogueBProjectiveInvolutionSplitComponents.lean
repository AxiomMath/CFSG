module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionProductQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitStructure

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K : Type*} [Field K] [Finite K]

theorem square_ordinaryCentralizer_pComponent_quasisimple
    (n : ℕ) (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (htwo : (2 : K) ≠ 0) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hsquare : IsSquare lambda.val) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Subgroup.centralizer {A})) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  obtain ⟨b, _, hr, hs, _, e, _, _, _, _⟩ :=
    square_projective_centralizer_structure n hn A lambda htwo hne hsq hsquare
  exact pComponent_quasisimple_of_equiv p e
    (CatalogueBProjectiveInvolutionProduct.generalLinear_product_pComponent_quasisimple
      (positiveMatrixDimension A b.val) (negativeMatrixDimension A b.val) K hr hs p hp) L hL

theorem square_projectiveCentralizer_pComponent_quasisimple
    (n : ℕ) (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (htwo : (2 : K) ≠ 0) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hsquare : IsSquare lambda.val) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A}))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let : Fact p.Prime := ⟨hp⟩
  exact projectiveCentralizer_pComponent_quasisimple_of_ordinary A p
    (square_ordinaryCentralizer_pComponent_quasisimple n hn A lambda htwo hne hsq hsquare p hp)
    L hL

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
