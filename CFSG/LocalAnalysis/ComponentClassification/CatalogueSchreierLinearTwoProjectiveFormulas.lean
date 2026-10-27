module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter Matrix Projectivization

universe u

@[expose] def coordinateGLAction (K : Type u) [Field K] :
    Matrix.GeneralLinearGroup (Fin 2) K →* Equiv.Perm (Omega K) :=
  (coordinatePGLAction K).comp Matrix.ProjGenLinGroup.mk

theorem coordinateGLAction_finite (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (x : K)
    (hden : A.val 1 0 * x + A.val 1 1 ≠ 0) :
    coordinateGLAction K A (some x) =
      some ((A.val 0 0 * x + A.val 0 1) / (A.val 1 0 * x + A.val 1 1)) := by
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk A) (some x)) = _
  rw [coordinatePGLAction_point, coordinateEquiv_some, coordinateEquiv_some,
    psl2AffinePoint, psl2AffinePoint, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨A.val 1 0 * x + A.val 1 1, ?_⟩
  change (A.val 1 0 * x + A.val 1 1) •
    (![(A.val 0 0 * x + A.val 0 1) / (A.val 1 0 * x + A.val 1 1), 1] : Fin 2 → K) =
      A.val *ᵥ ![x, 1]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_div_cancel₀ _ hden]

theorem coordinateGLAction_finite_denominator_zero (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (x : K)
    (hden : A.val 1 0 * x + A.val 1 1 = 0) :
    coordinateGLAction K A (some x) = none := by
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk A) (some x)) = _
  rw [coordinatePGLAction_point, coordinateEquiv_some, coordinateEquiv_none,
    psl2AffinePoint, psl2ProjectiveInfinity, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨A.val 0 0 * x + A.val 0 1, ?_⟩
  change (A.val 0 0 * x + A.val 0 1) • (![1, 0] : Fin 2 → K) = A.val *ᵥ ![x, 1]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, hden]

theorem coordinateGLAction_infinity (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (hc : A.val 1 0 ≠ 0) :
    coordinateGLAction K A none = some (A.val 0 0 / A.val 1 0) := by
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk A) none) = _
  rw [coordinatePGLAction_point, coordinateEquiv_none, coordinateEquiv_some,
    psl2ProjectiveInfinity, psl2AffinePoint, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨A.val 1 0, ?_⟩
  change A.val 1 0 • (![A.val 0 0 / A.val 1 0, 1] : Fin 2 → K) = A.val *ᵥ ![1, 0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_div_cancel₀ _ hc]

theorem coordinateGLAction_infinity_lower_left_zero (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (hc : A.val 1 0 = 0) :
    coordinateGLAction K A none = none := by
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinatePGLAction K (Matrix.ProjGenLinGroup.mk A) none) = _
  rw [coordinatePGLAction_point, coordinateEquiv_none,
    psl2ProjectiveInfinity, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨A.val 0 0, ?_⟩
  change A.val 0 0 • (![1, 0] : Fin 2 → K) = A.val *ᵥ ![1, 0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, hc]

theorem coordinateGLAction_range (K : Type u) [Field K] :
    (coordinateGLAction K).range = coordinateD K := coordinateGLAction_range_eq_D K

theorem coordinateG_orbit_infinity (K : Type u) [Field K] (x : Omega K) :
    ∃ g : coordinateG K, (g : Equiv.Perm (Omega K)) none = x := by
  cases x with
  | none => exact ⟨1, rfl⟩
  | some a =>
    refine ⟨⟨translation K a * inversion K, (coordinateG K).mul_mem
      (Subgroup.subset_closure (Or.inl ⟨a, rfl⟩))
      (Subgroup.subset_closure (Or.inr rfl))⟩, ?_⟩
    simp

theorem coordinateG_transitive (K : Type u) [Field K] (x y : Omega K) :
    ∃ g : coordinateG K, (g : Equiv.Perm (Omega K)) x = y := by
  obtain ⟨a, ha⟩ := coordinateG_orbit_infinity K x
  obtain ⟨b, hb⟩ := coordinateG_orbit_infinity K y
  refine ⟨b * a⁻¹, ?_⟩
  change (b : Equiv.Perm (Omega K)) ((a : Equiv.Perm (Omega K))⁻¹ x) = y
  rw [← ha]
  simpa using hb

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
