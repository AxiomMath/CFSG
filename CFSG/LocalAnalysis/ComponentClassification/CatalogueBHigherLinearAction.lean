module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearAction

noncomputable section

open Matrix

universe u

abbrev pslRange (n : ℕ) (K : Type u) [Field K] :
    Subgroup (Matrix.ProjGenLinGroup (Fin n) K) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin n) (R := K)).range

theorem slToPGL_kernel (n : ℕ) (K : Type u) [Field K] :
    (Matrix.SpecialLinearGroup.toPGL (n := Fin n) (R := K)).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
  Matrix.SpecialLinearGroup.toPGL_ker

theorem pslInclusion_injective (n : ℕ) (K : Type u) [Field K] :
    Function.Injective (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin n) (R := K)) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem pslRange_eq_map (n : ℕ) (K : Type u) [Field K] :
    pslRange n K = (CatalogueBGeneralLinear.specialLinearRange n K).map
      Matrix.ProjGenLinGroup.mk := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) y
    exact ⟨Matrix.SpecialLinearGroup.toGL g, ⟨g, rfl⟩,
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_mk g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk g, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk g⟩

instance pslRangeNormal (n : ℕ) (K : Type u) [Field K] : (pslRange n K).Normal := by
  rw [pslRange_eq_map]
  exact (inferInstance : (CatalogueBGeneralLinear.specialLinearRange n K).Normal).map
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

@[expose] def pslRangeEquiv (n : ℕ) (K : Type u) [Field K] :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* pslRange n K :=
  MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem pslRangeEquiv_val (n : ℕ) (K : Type u) [Field K]
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    (pslRangeEquiv n K x).val = Matrix.ProjectiveSpecialLinearGroup.toPGL x := rfl

theorem pslRangeEquiv_symm_toPGL (n : ℕ) (K : Type u) [Field K]
    (x : pslRange n K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL ((pslRangeEquiv n K).symm x) = x.val :=
  congrArg Subtype.val ((pslRangeEquiv n K).apply_symm_apply x)

@[expose] def pglAction (n : ℕ) (K : Type u) [Field K] :
    Matrix.ProjGenLinGroup (Fin n) K →*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  (MulAut.congr (pslRangeEquiv n K).symm).toMonoidHom.comp
    (MulAut.conjNormal (H := pslRange n K))

theorem toPGL_pglAction (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (pglAction n K a x) =
      a * Matrix.ProjectiveSpecialLinearGroup.toPGL x * a⁻¹ := by
  let e := pslRangeEquiv n K
  change ((e (e.symm ((MulAut.conjNormal (H := pslRange n K) a) (e x)))) :
    Matrix.ProjGenLinGroup (Fin n) K) = _
  rw [e.apply_symm_apply, MulAut.conjNormal_apply]
  rfl

theorem pglAction_toPGL (n : ℕ) (K : Type u) [Field K]
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    pglAction n K (Matrix.ProjectiveSpecialLinearGroup.toPGL x) = MulAut.conj x := by
  ext y
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction]
  simp [MulAut.conj_apply]

@[expose] def slConjugation (n : ℕ) (K : Type u) [Field K] :
    Matrix.GeneralLinearGroup (Fin n) K →*
      MulAut (Matrix.SpecialLinearGroup (Fin n) K) :=
  (MulAut.congr (CatalogueBGeneralLinear.rangeEquivSpecialLinear n K)).toMonoidHom.comp
    (MulAut.conjNormal (H := CatalogueBGeneralLinear.specialLinearRange n K))

theorem toGL_slConjugation (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.toGL (slConjugation n K A g) =
      A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ := by
  let e := CatalogueBGeneralLinear.specialLinearEquivRange n K
  change Matrix.SpecialLinearGroup.toGL
    (e.symm ((MulAut.conjNormal (H := CatalogueBGeneralLinear.specialLinearRange n K) A)
      (e g))) = _
  exact (CatalogueBGeneralLinear.rangeEquivSpecialLinear_toGL n K
    ((MulAut.conjNormal (H := CatalogueBGeneralLinear.specialLinearRange n K) A)
      (e g))).trans (MulAut.conjNormal_apply A (e g))

theorem slConjugation_matrix (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    (slConjugation n K A g : Matrix (Fin n) (Fin n) K) =
      A.val * (g : Matrix (Fin n) (Fin n) K) * (A⁻¹).val :=
  congrArg Units.val (toGL_slConjugation n K A g)

theorem slConjugation_entry (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) (i j : Fin n) :
    (slConjugation n K A g : Matrix (Fin n) (Fin n) K) i j =
      (A.val * (g : Matrix (Fin n) (Fin n) K) * (A⁻¹).val) i j :=
  congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j)
    (slConjugation_matrix n K A g)

theorem slConjugation_scalar (n : ℕ) (K : Type u) [Field K] (c : Kˣ) :
    slConjugation n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  apply MulEquiv.ext
  intro g
  change slConjugation n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) g = g
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, Matrix.GeneralLinearGroup.scalar_commute]
  simp

@[expose] def innerDiagonalAction (n : ℕ) (K : Type u) [Field K] :
    Matrix.GeneralLinearGroup (Fin n) K →*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  (pglAction n K).comp Matrix.ProjGenLinGroup.mk

theorem innerDiagonalAction_eq_pglAction (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    innerDiagonalAction n K A = pglAction n K (Matrix.ProjGenLinGroup.mk A) := rfl

theorem innerDiagonalAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    innerDiagonalAction n K A
        ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))) g) =
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)))
        (slConjugation n K A g) := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [innerDiagonalAction_eq_pglAction, toPGL_pglAction]
  change Matrix.ProjGenLinGroup.mk A *
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL g) *
    (Matrix.ProjGenLinGroup.mk A)⁻¹ =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (slConjugation n K A g))
  rw [toGL_slConjugation, map_mul, map_mul, map_inv]

theorem innerDiagonalAction_scalar (n : ℕ) (K : Type u) [Field K] (c : Kˣ) :
    innerDiagonalAction n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) = 1 := by
  rw [innerDiagonalAction_eq_pglAction, Matrix.ProjGenLinGroup.mk_scalar, map_one]

theorem innerDiagonalAction_mk_matrix (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    innerDiagonalAction n K A
        ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))) g) =
      QuotientGroup.mk (slConjugation n K A g) ∧
      (slConjugation n K A g : Matrix (Fin n) (Fin n) K) =
        A.val * (g : Matrix (Fin n) (Fin n) K) * (A⁻¹).val :=
  ⟨innerDiagonalAction_mk n K A g, slConjugation_matrix n K A g⟩

end

end CFSG.ComponentClassification.CatalogueBHigherLinearAction
