module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitExhaustion
public import Mathlib.GroupTheory.IndexNormal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type*} [Field K]

@[expose] def commonDeterminant : equalDeterminants K →* Kˣ where
  toFun z := Matrix.GeneralLinearGroup.det z.val.1
  map_one' := map_one _
  map_mul' z w := map_mul _ z.val.1 w.val.1

theorem commonDeterminant_apply (z : equalDeterminants K) :
    commonDeterminant z = Matrix.GeneralLinearGroup.det z.val.1 := rfl

theorem specialPairs_range : (specialPairs (K := K)).range = commonDeterminant.ker := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL w.1) = 1
    simp
  · intro hz
    have hA : z.val.1 ∈ (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker := hz
    have hB : z.val.2 ∈ (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker := by
      change Matrix.GeneralLinearGroup.det z.val.2 = 1
      rw [← z.property]
      exact hz
    rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hA hB
    obtain ⟨A, hA⟩ := hA
    obtain ⟨B, hB⟩ := hB
    exact ⟨(A, B), Subtype.ext (Prod.ext hA hB)⟩

theorem specialImage_le_leftRightImage : specialImage K ≤ leftRightImage K := by
  rintro g ⟨z, rfl⟩
  exact ⟨specialPairs z, rfl⟩

theorem leftRightImage_index_dvd_two : (leftRightImage K).index ∣ 2 := by
  apply Subgroup.index_dvd_two_iff.mpr
  refine ⟨tau, fun g => ?_⟩
  obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion g
  · exact Or.inr ⟨z, rfl⟩
  · exact Or.inl (by simpa only [mul_assoc, tau_mul_tau, mul_one] using
      (show rho z ∈ leftRightImage K from ⟨z, rfl⟩))

theorem leftRightImage_index_le_two : (leftRightImage K).index ≤ 2 :=
  Nat.le_of_dvd (by decide) leftRightImage_index_dvd_two

instance leftRightImageNormal : (leftRightImage K).Normal := by
  obtain h | h := Nat.prime_two.eq_one_or_self_of_dvd _
    (leftRightImage_index_dvd_two (K := K))
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

@[expose] def inverseTranspose (A : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup (Fin 2) K where
  val := (A⁻¹).val.transpose
  inv := A.val.transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem inverseTranspose_det (A : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (inverseTranspose A) =
      (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  change (A⁻¹).val.transpose.det = _
  rw [Matrix.det_transpose]
  exact congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det A)

@[expose] def transposePair (z : equalDeterminants K) : equalDeterminants K :=
  ⟨(inverseTranspose z.val.2, inverseTranspose z.val.1), by
    change Matrix.GeneralLinearGroup.det (inverseTranspose z.val.2) =
      Matrix.GeneralLinearGroup.det (inverseTranspose z.val.1)
    rw [inverseTranspose_det, inverseTranspose_det, z.property]⟩

theorem tau_rho_tau (z : equalDeterminants K) :
    tau * rho z * tau = rho (transposePair z) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change ((rho z).val X.transpose).transpose =
    (inverseTranspose z.val.2).val * X * (inverseTranspose z.val.1)⁻¹.val
  simp only [rho_apply, Matrix.transpose_mul, Matrix.transpose_transpose,
    inverseTranspose]
  exact (Matrix.mul_assoc _ _ _).symm

theorem commonDeterminant_transposePair (z : equalDeterminants K) :
    commonDeterminant (transposePair z) = (commonDeterminant z)⁻¹ := by
  change Matrix.GeneralLinearGroup.det (inverseTranspose z.val.2) =
    (Matrix.GeneralLinearGroup.det z.val.1)⁻¹
  rw [inverseTranspose_det, z.property]

theorem rho_mem_specialImage_of_commonDeterminant (z : equalDeterminants K)
    (hz : commonDeterminant z = 1) : rho z ∈ specialImage K := by
  have hz' : z ∈ (specialPairs (K := K)).range := by
    rw [specialPairs_range]
    exact hz
  obtain ⟨w, rfl⟩ := hz'
  exact ⟨w, rfl⟩

theorem rho_conjugation_mem_specialImage (z : equalDeterminants K)
    {g : DeterminantIsometries K} (hg : g ∈ specialImage K) :
    rho z * g * (rho z)⁻¹ ∈ specialImage K := by
  obtain ⟨w, rfl⟩ := hg
  change rho z * rho (specialPairs w) * (rho z)⁻¹ ∈ specialImage K
  rw [← map_inv, ← map_mul, ← map_mul]
  apply rho_mem_specialImage_of_commonDeterminant
  have hw : commonDeterminant (specialPairs w) = 1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL w.1) = 1
    simp
  rw [map_mul, map_mul, map_inv, hw, mul_one, mul_inv_cancel]

theorem tau_conjugation_mem_specialImage {g : DeterminantIsometries K}
    (hg : g ∈ specialImage K) : tau * g * tau ∈ specialImage K := by
  obtain ⟨w, rfl⟩ := hg
  change tau * rho (specialPairs w) * tau ∈ specialImage K
  rw [tau_rho_tau]
  apply rho_mem_specialImage_of_commonDeterminant
  rw [commonDeterminant_transposePair]
  have hw : commonDeterminant (specialPairs w) = 1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL w.1) = 1
    simp
  rw [hw, inv_one]

instance specialImageNormal : (specialImage K).Normal where
  conj_mem g hg u := by
    obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion u
    · exact rho_conjugation_mem_specialImage z hg
    · simpa only [_root_.mul_inv_rev, tau_inv, mul_assoc] using
        rho_conjugation_mem_specialImage z (tau_conjugation_mem_specialImage hg)

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
