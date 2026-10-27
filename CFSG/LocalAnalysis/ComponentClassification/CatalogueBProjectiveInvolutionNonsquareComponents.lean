module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponentsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveQuadraticStructure

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open CatalogueBProjectiveQuadratic

variable {K : Type*} [Field K] [Finite K]

theorem quadraticExtension_finite (lambda : K) : Finite (extension lambda) :=
  Module.finite_of_finite K

theorem nonsquare_ordinaryCentralizer_pComponent_quasisimple
    (n : ℕ) (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hns : ¬ IsSquare lambda.val)
    (p : ℕ) (L : Subgroup (Subgroup.centralizer {A}))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fact (¬ IsSquare lambda.val) := ⟨hns⟩
  let : Finite (extension lambda.val) := quadraticExtension_finite lambda.val
  have hm := (nonsquare_matrix_dimension n hn A lambda hsq hns).2
  exact pComponent_quasisimple_of_equiv p (matrixCentralizerQuadraticEquiv A lambda hsq)
    (CatalogueBGeneralLinear.pComponent_quasisimple
      (matrixDimension A lambda hsq) (extension lambda.val) hm p) L hL

theorem nonsquare_projectiveCentralizer_pComponent_quasisimple
    (n : ℕ) (hn : 2 ≤ n) (A : Matrix.GeneralLinearGroup (Fin n) K) (lambda : Kˣ)
    (hsq : A ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin n) lambda)
    (hns : ¬ IsSquare lambda.val) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A}))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let : Fact p.Prime := ⟨hp⟩
  exact projectiveCentralizer_pComponent_quasisimple_of_ordinary A p
    (nonsquare_ordinaryCentralizer_pComponent_quasisimple n hn A lambda hsq hns p) L hL

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
