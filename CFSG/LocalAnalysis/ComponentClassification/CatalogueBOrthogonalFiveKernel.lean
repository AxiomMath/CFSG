module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem selfAdjoint_commutant_scalar (h2 : (2 : K) ≠ 0)
    (g : Matrix (Fin 4) (Fin 4) K)
    (hg : ∀ X : selfAdjointSubmodule K, g * X.val = X.val * g) :
    g = Matrix.scalar (Fin 4) (g 0 0) := by
  have hU := hg (selfAdjointCoordinates h2 ![0, 0, 0, 1, 0])
  have hV := hg (selfAdjointCoordinates h2 ![0, 0, 0, 0, 1])
  have hE := hg (selfAdjointCoordinates h2 ![0, 1, 0, 0, 0])
  have hF := hg (selfAdjointCoordinates h2 ![0, 0, 1, 0, 0])
  have h30 : g 3 0 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hU).symm
  have h31 : g 3 1 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hU).symm
  have h20 : g 2 0 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 0) hU).symm
  have h21 : g 2 1 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 1) hU).symm
  have h03 : g 0 3 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hV)
  have h02 : g 0 2 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hV)
  have h13 : g 1 3 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 0) hV)
  have h12 : g 1 2 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 1) hV)
  have h10 : g 1 0 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hE).symm
  have h01 : g 0 1 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) hF)
  have h23 : g 2 3 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 2 2) hE)
  have h32 : g 3 2 = 0 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 2 2) hF).symm
  have hdiag11 : g 0 0 = g 1 1 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 1) hE)
  have hdiag33 : g 0 0 = g 3 3 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 3) hU)
  have hdiag22 : g 1 1 = g 2 2 := by
    simpa [selfAdjointCoordinates, Matrix.mul_apply, Fin.sum_univ_four] using
      (congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 1 2) hU)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar, h01, h02, h03, h10, h12, h13, h20, h21, h23,
      h30, h31, h32, ← hdiag11, ← hdiag22, ← hdiag33]

@[expose] def selfAdjointScalarSimilitude (c : Kˣ) : symplecticSimilitudes K :=
  ⟨GeneralLinearGroup.scalar (Fin 4) c, c ^ 2, by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_two]
    rfl⟩

theorem selfAdjointOrthogonalAction_scalar (h2 : (2 : K) ≠ 0) (c : Kˣ) :
    selfAdjointOrthogonalAction h2 (selfAdjointScalarSimilitude c) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (GeneralLinearGroup.scalar (Fin 4) c).val * X.val *
    (GeneralLinearGroup.scalar (Fin 4) c)⁻¹.val = X.val
  have hc : (GeneralLinearGroup.scalar (Fin 4) c).val * X.val =
      X.val * (GeneralLinearGroup.scalar (Fin 4) c).val := by
    rw [GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_comm (c : K) (Commute.all _) X.val
  rw [hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem selfAdjointOrthogonalAction_eq_one_iff (h2 : (2 : K) ≠ 0)
    (A : symplecticSimilitudes K) :
    selfAdjointOrthogonalAction h2 A = 1 ↔
      ∃ c : Kˣ, A.val = GeneralLinearGroup.scalar (Fin 4) c := by
  constructor
  · intro hA
    have hg (X : selfAdjointSubmodule K) : A.val.val * X.val = X.val * A.val.val := by
      have h : A.val.val * X.val * A.val⁻¹.val = X.val :=
        congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) =>
          (g.val X).val) hA
      have h' := congrArg (fun Z : Matrix (Fin 4) (Fin 4) K => Z * A.val.val) h
      simpa only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] using h'
    have hs : A.val ∈ Subgroup.center (GL (Fin 4) K) :=
      GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
        ⟨A.val.val 0 0, (selfAdjoint_commutant_scalar h2 A.val.val hg).symm⟩
    rw [GeneralLinearGroup.center_eq_range_scalar] at hs
    obtain ⟨c, hc⟩ := hs
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have he : A = selfAdjointScalarSimilitude c := Subtype.ext hc
    rw [he]
    exact selfAdjointOrthogonalAction_scalar h2 c

theorem symplecticMultiplier_scalar (c : Kˣ) :
    symplecticMultiplier (selfAdjointScalarSimilitude c) = c ^ 2 := by
  apply symplectic_multiplier_unique _ _ _ (symplecticMultiplier_spec _)
  change (GeneralLinearGroup.scalar (Fin 4) c).valᵀ * symplecticGram K *
    (GeneralLinearGroup.scalar (Fin 4) c).val = ((c ^ 2 : Kˣ) : K) • symplecticGram K
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_two]
  rfl

theorem selfAdjointOrthogonalAction_symplectic_kernel (h2 : (2 : K) ≠ 0)
    (A : symplecticMultiplier.ker) :
    selfAdjointOrthogonalAction h2 A.val = 1 ↔
      ∃ c : Kˣ, c ^ 2 = 1 ∧ A.val.val = GeneralLinearGroup.scalar (Fin 4) c := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ := (selfAdjointOrthogonalAction_eq_one_iff h2 A.val).mp hA
    have he : A.val = selfAdjointScalarSimilitude c := Subtype.ext hc
    refine ⟨c, ?_, hc⟩
    have hm := symplecticMultiplier.mem_ker.mp A.property
    rw [he, symplecticMultiplier_scalar] at hm
    exact hm
  · rintro ⟨c, _, hc⟩
    exact (selfAdjointOrthogonalAction_eq_one_iff h2 A.val).mpr ⟨c, hc⟩

@[expose] def selfAdjointSymplecticAction (h2 : (2 : K) ≠ 0) :
    (symplecticMultiplier (K := K)).ker →*
      TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) :=
  (selfAdjointOrthogonalAction h2).comp (symplecticMultiplier (K := K)).ker.subtype

theorem selfAdjointSymplecticAction_kernel_sign (h2 : (2 : K) ≠ 0)
    (A : (symplecticMultiplier (K := K)).ker) :
    selfAdjointSymplecticAction h2 A = 1 ↔
      A.val.val.val = (1 : Matrix (Fin 4) (Fin 4) K) ∨
        A.val.val.val = -(1 : Matrix (Fin 4) (Fin 4) K) := by
  constructor
  · intro hA
    obtain ⟨c, hc, hscalar⟩ := (selfAdjointOrthogonalAction_symplectic_kernel h2 A).mp hA
    have hs : c = 1 ∨ c = -1 :=
      Units.eq_or_eq_neg_of_sq_eq_sq c 1 (by simpa using hc)
    rcases hs with rfl | rfl
    · exact Or.inl (by rw [hscalar, map_one]; rfl)
    · apply Or.inr
      rw [hscalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact neg_one_smul K _
  · intro hA
    apply (selfAdjointOrthogonalAction_symplectic_kernel h2 A).mpr
    rcases hA with hA | hA
    · refine ⟨1, by simp, ?_⟩
      apply Units.ext
      simpa using hA
    · refine ⟨-1, by simp [pow_two], ?_⟩
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hA.trans (neg_one_smul K _).symm

theorem selfAdjointSymplecticAction_kernel_le_center (h2 : (2 : K) ≠ 0) :
    (selfAdjointSymplecticAction h2).ker ≤
      Subgroup.center (symplecticMultiplier (K := K)).ker := by
  intro A hA
  obtain ⟨c, _, hc⟩ := (selfAdjointOrthogonalAction_symplectic_kernel h2 A).mp hA
  apply Subgroup.mem_center_iff.mpr
  intro B
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change B.val.val.val * A.val.val.val = A.val.val.val * B.val.val.val
  rw [hc, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_comm (c : K) (Commute.all _) B.val.val.val).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
