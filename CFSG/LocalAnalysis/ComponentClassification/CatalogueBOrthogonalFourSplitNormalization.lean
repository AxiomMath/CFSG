module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open Matrix QuadraticMap

variable {K : Type*} [Field K]

@[expose] def matrixUnit (i j : Fin 2) : Matrix (Fin 2) (Fin 2) K := Matrix.single i j 1

theorem matrixUnit_det (i j : Fin 2) : (matrixUnit (K := K) i j).det = 0 := by
  fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single, Matrix.det_fin_two]

theorem matrixUnit_sum_diag : matrixUnit (K := K) 0 0 + matrixUnit 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single]

theorem determinant_polar_one (X : Matrix (Fin 2) (Fin 2) K) :
    polar (determinantForm K) 1 X = X.trace := by
  rw [determinantForm_polar, Matrix.trace_fin_two]
  simp [add_comm]

theorem determinantIsometry_det (g : DeterminantIsometries K)
    (X : Matrix (Fin 2) (Fin 2) K) : (g.val X).det = X.det := by
  simpa only [determinantForm_apply] using
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.property X

theorem determinantIsometry_polar (g : DeterminantIsometries K)
    (X Y : Matrix (Fin 2) (Fin 2) K) :
    polar (determinantForm K) (g.val X) (g.val Y) = polar (determinantForm K) X Y :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.property X Y

theorem determinantIsometry_trace (g : DeterminantIsometries K) (h1 : g.val 1 = 1)
    (X : Matrix (Fin 2) (Fin 2) K) : (g.val X).trace = X.trace := by
  rw [← determinant_polar_one, ← h1, determinantIsometry_polar, determinant_polar_one]

theorem exists_projector_conjugating_matrix (X : Matrix (Fin 2) (Fin 2) K)
    (htr : X.trace = 1) (hdet : X.det = 0) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) K,
      X * P.val = P.val * matrixUnit 0 0 := by
  have hsum : X 0 0 + X 1 1 = 1 := by simpa only [Matrix.trace_fin_two] using htr
  have hprod : X 0 0 * X 1 1 = X 0 1 * X 1 0 := by
    simpa only [Matrix.det_fin_two, sub_eq_zero] using hdet
  by_cases ha : X 0 0 = 0
  · have hd : X 1 1 = 1 := by simpa [ha] using hsum
    let P : Matrix (Fin 2) (Fin 2) K := !![X 0 1, X 1 1; X 1 1, -X 1 0]
    have hp : P.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change X 0 1 * (-X 1 0) - X 1 1 * X 1 1 ≠ 0
      rw [mul_neg, ← hprod, ha, zero_mul, neg_zero, hd]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, matrixUnit, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two, ha, hd]
    all_goals
      have hbc : X 0 1 * X 1 0 = 0 := by simpa [ha] using hprod.symm
      first | exact mul_eq_zero.mp hbc | exact (mul_eq_zero.mp hbc).symm
  · let P : Matrix (Fin 2) (Fin 2) K := !![X 0 0, -X 0 1; X 1 0, X 0 0]
    have hp : P.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change X 0 0 * X 0 0 - (-X 0 1) * X 1 0 ≠ 0
      have he : X 0 0 * X 0 0 - (-X 0 1) * X 1 0 = X 0 0 := by
        linear_combination X 0 0 * hsum - hprod
      rwa [he]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, matrixUnit, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination X 0 0 * hsum - hprod
    · ring
    · linear_combination X 1 0 * hsum
    · linear_combination hprod

@[expose] def conjugationPair (P : Matrix.GeneralLinearGroup (Fin 2) K) :
    equalDeterminants K := ⟨(P, P), rfl⟩

theorem rho_conjugationPair_one (P : Matrix.GeneralLinearGroup (Fin 2) K) :
    (rho (conjugationPair P)).val 1 = 1 := by
  simp [rho_apply, conjugationPair]

theorem rho_conjugationPair_projector
    (X : Matrix (Fin 2) (Fin 2) K) (P : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : X * P.val = P.val * matrixUnit 0 0) :
    (rho (conjugationPair P⁻¹)).val X = matrixUnit 0 0 := by
  have hx := congrArg (fun Y => (P⁻¹).val * Y) h
  have he : (P⁻¹).val * X * P.val = matrixUnit 0 0 := by
    simpa [Matrix.mul_assoc, Units.inv_mul] using hx
  simpa only [rho_apply, conjugationPair, inv_inv] using he

theorem exists_normalized_isometry (g : DeterminantIsometries K) :
    ∃ z : equalDeterminants K, ∃ h : DeterminantIsometries K,
      g = rho z * h ∧ h.val 1 = 1 ∧ h.val (matrixUnit 0 0) = matrixUnit 0 0 := by
  have hdet : (g.val 1).det = 1 := by simpa using determinantIsometry_det g 1
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero (g.val 1) (by rw [hdet]; exact one_ne_zero)
  let a : equalDeterminants K := ⟨(A, 1), (mem_equalDeterminants A 1).mpr (by simpa [A] using hdet)⟩
  let u : DeterminantIsometries K := (rho a)⁻¹ * g
  have hu1 : u.val 1 = 1 := by
    have hval : (rho a).val 1 = g.val 1 := by simp [rho_apply, a, A]
    change (rho a).val.symm (g.val 1) = 1
    rw [← hval]
    exact (rho a).val.symm_apply_apply 1
  have hxtr : (u.val (matrixUnit 0 0)).trace = 1 := by
    rw [determinantIsometry_trace u hu1]
    simp [matrixUnit, Matrix.single, Matrix.trace_fin_two]
  obtain ⟨P, hP⟩ := exists_projector_conjugating_matrix (u.val (matrixUnit 0 0)) hxtr
    (by rw [determinantIsometry_det, matrixUnit_det])
  let c := conjugationPair P⁻¹
  let h : DeterminantIsometries K := rho c * u
  refine ⟨a * c⁻¹, h, ?_, ?_, ?_⟩
  · dsimp [h, u]
    rw [map_mul, map_inv]
    group
  · change (rho c).val (u.val 1) = 1
    rw [hu1]
    exact rho_conjugationPair_one P⁻¹
  · exact rho_conjugationPair_projector _ P hP

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
