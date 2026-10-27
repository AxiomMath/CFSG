module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

abbrev glGraphAut (n : ℕ) (K : Type u) [Field K] :
    MulAut (GL (Fin n) K) := Matrix.GeneralLinearGroup.inverseTranspose

theorem glGraphAut_matrix (n : ℕ) (K : Type u) [Field K] (g : GL (Fin n) K) :
    (glGraphAut n K g).val = (g⁻¹).val.transpose :=
  Matrix.GeneralLinearGroup.coe_inverseTranspose g

private theorem toGL_inverseTranspose (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.toGL (g⁻¹).transpose =
      glGraphAut n K (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rw [glGraphAut_matrix]
  change ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
    ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val.transpose
  rw [← map_inv]
  rfl

@[expose] def slGraphAut (n : ℕ) (K : Type u) [Field K] :
    MulAut (Matrix.SpecialLinearGroup (Fin n) K) where
  toFun g := (g⁻¹).transpose
  invFun g := (g⁻¹).transpose
  left_inv g := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_inverseTranspose, toGL_inverseTranspose]
    exact Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose _
  right_inv g := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_inverseTranspose, toGL_inverseTranspose]
    exact Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose _
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_inverseTranspose, map_mul Matrix.SpecialLinearGroup.toGL,
      map_mul Matrix.SpecialLinearGroup.toGL, toGL_inverseTranspose, toGL_inverseTranspose]
    exact map_mul (glGraphAut n K) _ _

theorem toGL_slGraphAut (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.toGL (slGraphAut n K g) =
      glGraphAut n K (Matrix.SpecialLinearGroup.toGL g) :=
  toGL_inverseTranspose n K g

theorem slGraphAut_matrix (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    (slGraphAut n K g : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose := rfl

@[expose] def pglGraphAut (n : ℕ) (K : Type u) [Field K] :
    MulAut (Matrix.ProjGenLinGroup (Fin n) K) :=
  QuotientGroup.congr _ _ (glGraphAut n K) (Subgroup.map_center_eq (glGraphAut n K))

theorem pglGraphAut_mk (n : ℕ) (K : Type u) [Field K] (g : GL (Fin n) K) :
    pglGraphAut n K (Matrix.ProjGenLinGroup.mk g) =
      Matrix.ProjGenLinGroup.mk (glGraphAut n K g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

@[expose] def pslGraphAut (n : ℕ) (K : Type u) [Field K] :
    MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  QuotientGroup.congr _ _ (slGraphAut n K) (Subgroup.map_center_eq (slGraphAut n K))

theorem pslGraphAut_mk (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    pslGraphAut n K (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) g) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
        (slGraphAut n K g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

theorem pslGraphAut_mk_inverseTranspose (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    pslGraphAut n K (QuotientGroup.mk g) = QuotientGroup.mk (g⁻¹).transpose :=
  pslGraphAut_mk n K g

theorem glGraphAut_scalar (n : ℕ) (K : Type u) [Field K] (c : Kˣ) :
    glGraphAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ := by
  apply Units.ext
  rw [glGraphAut_matrix, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar, Matrix.transpose_apply, Matrix.diagonal_apply, eq_comm]

theorem toPGL_pslGraphAut (n : ℕ) (K : Type u) [Field K]
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (pslGraphAut n K x) =
      pglGraphAut n K (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) x
  rw [pslGraphAut_mk]
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (slGraphAut n K g)) =
    pglGraphAut n K (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL g))
  rw [pglGraphAut_mk]
  exact congrArg Matrix.ProjGenLinGroup.mk (toGL_slGraphAut n K g)

theorem glGraphAut_sq (n : ℕ) (K : Type u) [Field K] : glGraphAut n K ^ 2 = 1 := by
  apply MulEquiv.ext
  intro g
  change glGraphAut n K (glGraphAut n K g) = g
  exact Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose g

theorem slGraphAut_sq (n : ℕ) (K : Type u) [Field K] : slGraphAut n K ^ 2 = 1 := by
  apply MulEquiv.ext
  intro g
  change slGraphAut n K (slGraphAut n K g) = g
  exact (slGraphAut n K).left_inv g

theorem pglGraphAut_sq (n : ℕ) (K : Type u) [Field K] : pglGraphAut n K ^ 2 = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  change pglGraphAut n K (pglGraphAut n K (Matrix.ProjGenLinGroup.mk g)) = _
  rw [pglGraphAut_mk, pglGraphAut_mk]
  exact congrArg Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose g)

theorem pslGraphAut_sq (n : ℕ) (K : Type u) [Field K] : pslGraphAut n K ^ 2 = 1 := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL (pslGraphAut n K (pslGraphAut n K x)) = _
  rw [toPGL_pslGraphAut, toPGL_pslGraphAut]
  exact DFunLike.congr_fun (pglGraphAut_sq n K) (Matrix.ProjectiveSpecialLinearGroup.toPGL x)

theorem glGraphAut_field_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    glGraphAut n K (glFieldAut (Fin n) K sigma g) =
      glFieldAut (Fin n) K sigma (glGraphAut n K g) :=
  (Matrix.GeneralLinearGroup.map_inverseTranspose sigma.toRingHom g).symm

theorem slGraphAut_field_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    slGraphAut n K (slFieldAut (Fin n) K sigma g) =
      slFieldAut (Fin n) K sigma (slGraphAut n K g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  change Matrix.SpecialLinearGroup.toGL (slGraphAut n K (slFieldEquiv (Fin n) sigma g)) =
    Matrix.SpecialLinearGroup.toGL (slFieldEquiv (Fin n) sigma (slGraphAut n K g))
  rw [toGL_slGraphAut, toGL_slFieldEquiv, toGL_slFieldEquiv, toGL_slGraphAut]
  exact glGraphAut_field_commute n K sigma _

theorem pglGraphAut_field_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    pglGraphAut n K * pglFieldAut (Fin n) K sigma =
      pglFieldAut (Fin n) K sigma * pglGraphAut n K := by
  ext x
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  change pglGraphAut n K (pglFieldEquiv (Fin n) sigma (Matrix.ProjGenLinGroup.mk g)) =
    pglFieldEquiv (Fin n) sigma (pglGraphAut n K (Matrix.ProjGenLinGroup.mk g))
  rw [pglFieldEquiv_mk, pglGraphAut_mk, pglGraphAut_mk, pglFieldEquiv_mk]
  exact congrArg Matrix.ProjGenLinGroup.mk (glGraphAut_field_commute n K sigma g)

theorem pslGraphAut_field_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    pslGraphAut n K * pslFieldAut (Fin n) K sigma =
      pslFieldAut (Fin n) K sigma * pslGraphAut n K := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (pslGraphAut n K (pslFieldAut (Fin n) K sigma x)) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (pslFieldAut (Fin n) K sigma (pslGraphAut n K x))
  rw [toPGL_pslGraphAut, toPGL_pslFieldAut, toPGL_pslFieldAut, toPGL_pslGraphAut]
  exact DFunLike.congr_fun (pglGraphAut_field_commute n K sigma)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL x)

theorem graph_innerDiagonal_commute (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) :
    pslGraphAut n K * innerDiagonalAction n K A =
      innerDiagonalAction n K (glGraphAut n K A) * pslGraphAut n K := by
  ext x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL (pslGraphAut n K (innerDiagonalAction n K A x)) =
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (innerDiagonalAction n K (glGraphAut n K A) (pslGraphAut n K x))
  rw [toPGL_pslGraphAut, innerDiagonalAction_eq_pglAction, toPGL_pglAction,
    innerDiagonalAction_eq_pglAction, toPGL_pglAction, toPGL_pslGraphAut,
    map_mul, map_mul, map_inv, pglGraphAut_mk]

@[expose] def pureGraphAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  innerDiagonalAction n K A * pslGraphAut n K

theorem pureGraphAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    pureGraphAction n K A (QuotientGroup.mk g) =
      QuotientGroup.mk (slConjugation n K A (g⁻¹).transpose) := by
  change innerDiagonalAction n K A (pslGraphAut n K (QuotientGroup.mk g)) = _
  rw [pslGraphAut_mk_inverseTranspose]
  exact innerDiagonalAction_mk n K A (g⁻¹).transpose

@[expose] def pglPureGraphAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) : MulAut (Matrix.ProjGenLinGroup (Fin n) K) :=
  MulAut.conj (Matrix.ProjGenLinGroup.mk A) * pglGraphAut n K

theorem pglPureGraphAction_mk (n : ℕ) (K : Type u) [Field K]
    (A g : GL (Fin n) K) :
    pglPureGraphAction n K A (Matrix.ProjGenLinGroup.mk g) =
      Matrix.ProjGenLinGroup.mk (A * glGraphAut n K g * A⁻¹) := by
  change MulAut.conj (Matrix.ProjGenLinGroup.mk A)
    (pglGraphAut n K (Matrix.ProjGenLinGroup.mk g)) = _
  rw [pglGraphAut_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem toPGL_pureGraphAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (pureGraphAction n K A x) =
      pglPureGraphAction n K A (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (innerDiagonalAction n K A (pslGraphAut n K x)) =
      MulAut.conj (Matrix.ProjGenLinGroup.mk A)
        (pglGraphAut n K (Matrix.ProjectiveSpecialLinearGroup.toPGL x))
  rw [innerDiagonalAction_eq_pglAction, toPGL_pglAction, toPGL_pslGraphAut,
    MulAut.conj_apply]

theorem pureGraphAction_mul (n : ℕ) (K : Type u) [Field K]
    (A B : GL (Fin n) K) :
    pureGraphAction n K A * pureGraphAction n K B =
      innerDiagonalAction n K (A * glGraphAut n K B) := by
  unfold pureGraphAction
  calc
    _ = innerDiagonalAction n K A *
        (pslGraphAut n K * innerDiagonalAction n K B) * pslGraphAut n K := by group
    _ = innerDiagonalAction n K A *
        (innerDiagonalAction n K (glGraphAut n K B) * pslGraphAut n K) *
        pslGraphAut n K := by rw [graph_innerDiagonal_commute]
    _ = innerDiagonalAction n K A * innerDiagonalAction n K (glGraphAut n K B) *
        pslGraphAut n K ^ 2 := by rw [pow_two]; group
    _ = innerDiagonalAction n K (A * glGraphAut n K B) := by
      rw [pslGraphAut_sq, mul_one, map_mul]

theorem pureGraphAction_sq (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) :
    pureGraphAction n K A ^ 2 = innerDiagonalAction n K (A * glGraphAut n K A) := by
  rw [pow_two, pureGraphAction_mul]

end

end CFSG.ComponentClassification.CatalogueBGraphForm
