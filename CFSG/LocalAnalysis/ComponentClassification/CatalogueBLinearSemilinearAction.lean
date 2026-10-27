module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

namespace CFSG.ComponentClassification.CatalogueBLinearSemilinear

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField

universe u

@[expose] def slSemilinearAction (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K) :
    MulAut (SpecialLinearGroup (Fin n) K) :=
  slConjugation n K A * slFieldAut (Fin n) K sigma

@[expose] def semilinearAction (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K) :
    MulAut (ProjectiveSpecialLinearGroup (Fin n) K) :=
  innerDiagonalAction n K A * pslFieldAut (Fin n) K sigma

theorem slSemilinearAction_toGL (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (slSemilinearAction n K A sigma g) =
      A * glFieldAut (Fin n) K sigma (SpecialLinearGroup.toGL g) * A⁻¹ := by
  change SpecialLinearGroup.toGL
    (slConjugation n K A (slFieldAut (Fin n) K sigma g)) = _
  rw [toGL_slConjugation]
  congr 2
  exact toGL_slFieldEquiv (Fin n) sigma g

theorem slSemilinearAction_matrix (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (g : SpecialLinearGroup (Fin n) K) :
    (slSemilinearAction n K A sigma g : Matrix (Fin n) (Fin n) K) =
      A.val * sigma.toRingHom.mapMatrix g * (A⁻¹).val :=
  congrArg Units.val (slSemilinearAction_toGL n K A sigma g)

theorem semilinearAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K)
    (g : SpecialLinearGroup (Fin n) K) :
    semilinearAction n K A sigma
        ((QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))) g) =
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)))
        (slSemilinearAction n K A sigma g) := by
  change innerDiagonalAction n K A
    (pslFieldAut (Fin n) K sigma (QuotientGroup.mk g)) = _
  have hfield := pslFieldAut_mk (Fin n) K sigma g
  rw [hfield]
  exact innerDiagonalAction_mk n K A (slFieldAut (Fin n) K sigma g)

theorem slSemilinearAction_mul (n : ℕ) (K : Type u) [Field K]
    (A B : GeneralLinearGroup (Fin n) K) (sigma rho : K ≃+* K) :
    slSemilinearAction n K A sigma * slSemilinearAction n K B rho =
      slSemilinearAction n K (A * glFieldAut (Fin n) K sigma B) (sigma * rho) := by
  apply MulEquiv.ext
  intro g
  apply SpecialLinearGroup.toGL_injective
  change SpecialLinearGroup.toGL
    (slSemilinearAction n K A sigma (slSemilinearAction n K B rho g)) = _
  rw [slSemilinearAction_toGL, slSemilinearAction_toGL,
    slSemilinearAction_toGL, map_mul, map_mul, map_inv]
  have hfield : glFieldAut (Fin n) K (sigma * rho) (SpecialLinearGroup.toGL g) =
      glFieldAut (Fin n) K sigma
        (glFieldAut (Fin n) K rho (SpecialLinearGroup.toGL g)) := by
    rw [map_mul]
    rfl
  rw [hfield]
  group

theorem semilinearAction_mul (n : ℕ) (K : Type u) [Field K]
    (A B : GeneralLinearGroup (Fin n) K) (sigma rho : K ≃+* K) :
    semilinearAction n K A sigma * semilinearAction n K B rho =
      semilinearAction n K (A * glFieldAut (Fin n) K sigma B) (sigma * rho) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin n) K)) x
  change semilinearAction n K A sigma
    (semilinearAction n K B rho
      ((QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))) g)) = _
  rw [semilinearAction_mk, semilinearAction_mk, semilinearAction_mk]
  exact congrArg (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)))
    (DFunLike.congr_fun (slSemilinearAction_mul n K A B sigma rho) g)

theorem semilinearAction_sq (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) (sigma : K ≃+* K) :
    semilinearAction n K A sigma ^ 2 =
      semilinearAction n K (A * glFieldAut (Fin n) K sigma A) (sigma ^ 2) := by
  simpa only [pow_two] using semilinearAction_mul n K A A sigma sigma

theorem semilinearAction_one_field (n : ℕ) (K : Type u) [Field K]
    (A : GeneralLinearGroup (Fin n) K) :
    semilinearAction n K A 1 = innerDiagonalAction n K A := by
  simp [semilinearAction]

theorem semilinearAction_scalar (n : ℕ) (K : Type u) [Field K]
    (c : Kˣ) (sigma : K ≃+* K) :
    semilinearAction n K (GeneralLinearGroup.scalar (Fin n) c) sigma =
      pslFieldAut (Fin n) K sigma := by
  rw [semilinearAction, innerDiagonalAction_scalar, one_mul]

end

end CFSG.ComponentClassification.CatalogueBLinearSemilinear
