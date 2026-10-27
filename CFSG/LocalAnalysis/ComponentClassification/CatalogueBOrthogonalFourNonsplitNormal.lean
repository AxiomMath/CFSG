module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExhaustion

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K] (delta : K) [Finite K] [Fact (¬ IsSquare delta)]

@[expose] def domainDeterminant : normDeterminantOne delta →* (extension delta)ˣ :=
  Matrix.GeneralLinearGroup.det.comp (normDeterminantOne delta).subtype

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem specialMatrices_range : (specialMatrices delta).range = (domainDeterminant delta).ker := by
  ext A
  constructor
  · rintro ⟨S, rfl⟩
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL S) = 1
    simp
  · intro hA
    have hA' : A.val ∈ (Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (extension delta) →* (extension delta)ˣ).ker := hA
    rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hA'
    obtain ⟨S, hS⟩ := hA'
    exact ⟨S, Subtype.ext hS⟩

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem specialImage_le_congruenceImage (h2 : (2 : K) ≠ 0) :
    specialImage delta h2 ≤ congruenceImage delta h2 := by
  rintro g ⟨S, rfl⟩
  exact ⟨specialMatrices delta S, rfl⟩

theorem congruenceImage_index_dvd_two (h2 : (2 : K) ≠ 0) :
    (congruenceImage delta h2).index ∣ 2 := by
  apply Subgroup.index_dvd_two_iff.mpr
  refine ⟨gamma delta h2, fun g => ?_⟩
  obtain ⟨A, rfl | rfl⟩ := hermitian_isometry_exhaustion delta h2 g
  · exact Or.inr ⟨A, rfl⟩
  · exact Or.inl (by simpa only [mul_assoc, gamma_mul_gamma, mul_one] using
      (show rho delta h2 A ∈ congruenceImage delta h2 from ⟨A, rfl⟩))

theorem congruenceImage_index_le_two (h2 : (2 : K) ≠ 0) :
    (congruenceImage delta h2).index ≤ 2 :=
  Nat.le_of_dvd (by decide) (congruenceImage_index_dvd_two delta h2)

instance congruenceImageNormal (h2 : (2 : K) ≠ 0) : (congruenceImage delta h2).Normal := by
  obtain h | h := Nat.prime_two.eq_one_or_self_of_dvd _
    (congruenceImage_index_dvd_two delta h2)
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem domainDeterminant_conjugateD (A : normDeterminantOne delta) :
    domainDeterminant delta (conjugateD delta A) =
      Units.map (conjugation delta).toRingHom (domainDeterminant delta A) := by
  change Matrix.GeneralLinearGroup.det (conjugateGL delta A.val) = _
  exact Matrix.GeneralLinearGroup.map_det _ _

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem rho_mem_specialImage_of_determinant (h2 : (2 : K) ≠ 0)
    (A : normDeterminantOne delta) (hA : domainDeterminant delta A = 1) :
    rho delta h2 A ∈ specialImage delta h2 := by
  have hA' : A ∈ (specialMatrices delta).range := by
    rw [specialMatrices_range]
    exact hA
  obtain ⟨S, rfl⟩ := hA'
  exact ⟨S, rfl⟩

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem rho_conjugation_mem_specialImage (h2 : (2 : K) ≠ 0)
    (A : normDeterminantOne delta) {g : HermitianIsometries delta}
    (hg : g ∈ specialImage delta h2) :
    rho delta h2 A * g * (rho delta h2 A)⁻¹ ∈ specialImage delta h2 := by
  obtain ⟨S, rfl⟩ := hg
  change rho delta h2 A * rho delta h2 (specialMatrices delta S) *
    (rho delta h2 A)⁻¹ ∈ specialImage delta h2
  rw [← map_inv, ← map_mul, ← map_mul]
  apply rho_mem_specialImage_of_determinant
  have hS : domainDeterminant delta (specialMatrices delta S) = 1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL S) = 1
    simp
  rw [map_mul, map_mul, map_inv, hS, mul_one, mul_inv_cancel]

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem gamma_conjugation_mem_specialImage (h2 : (2 : K) ≠ 0)
    {g : HermitianIsometries delta} (hg : g ∈ specialImage delta h2) :
    gamma delta h2 * g * gamma delta h2 ∈ specialImage delta h2 := by
  obtain ⟨S, rfl⟩ := hg
  change gamma delta h2 * rho delta h2 (specialMatrices delta S) *
    gamma delta h2 ∈ specialImage delta h2
  rw [gamma_rho, mul_assoc, gamma_mul_gamma, mul_one]
  apply rho_mem_specialImage_of_determinant
  rw [domainDeterminant_conjugateD]
  have hS : domainDeterminant delta (specialMatrices delta S) = 1 := by
    change Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL S) = 1
    simp
  rw [hS, map_one]

instance specialImageNormal (h2 : (2 : K) ≠ 0) : (specialImage delta h2).Normal where
  conj_mem g hg u := by
    obtain ⟨A, rfl | rfl⟩ := hermitian_isometry_exhaustion delta h2 u
    · exact rho_conjugation_mem_specialImage delta h2 A hg
    · simpa only [_root_.mul_inv_rev, gamma_inv, mul_assoc] using
        rho_conjugation_mem_specialImage delta h2 A
          (gamma_conjugation_mem_specialImage delta h2 hg)

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
