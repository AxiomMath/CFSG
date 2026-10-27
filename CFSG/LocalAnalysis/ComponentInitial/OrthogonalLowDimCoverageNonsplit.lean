module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type*} [Field K] (delta : K) [Fact (¬ IsSquare delta)]

omit [Fact (¬ IsSquare delta)] in
theorem rho_mem_specialImage_of_domainDeterminant_eq_sq (h2 : (2 : K) ≠ 0)
    (A : normDeterminantOne delta) {c : (extension delta)ˣ}
    (hc : QuadraticAlgebra.norm (c : extension delta) = 1)
    (hA : domainDeterminant delta A = c ^ 2) : rho delta h2 A ∈ specialImage delta h2 := by
  have hc' : QuadraticAlgebra.norm ((c⁻¹ : (extension delta)ˣ) : extension delta) = 1 := by
    have h := map_mul (QuadraticAlgebra.norm : extension delta →* K)
      ((c⁻¹ : (extension delta)ˣ) : extension delta) (c : extension delta)
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, hc, mul_one] at h
    exact h.symm
  have h := rho_mem_specialImage_of_determinant delta h2 (A * scalarD delta c⁻¹ hc') (by
    rw [map_mul, hA]
    change c ^ 2 * GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) c⁻¹) = 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, mul_inv_cancel])
  rwa [map_mul, rho_scalarD, mul_one] at h

variable [Finite K]

theorem hermitian_sq_mem_specialImage (h2 : (2 : K) ≠ 0) (g : HermitianIsometries delta) :
    g ^ 2 ∈ specialImage delta h2 := by
  obtain ⟨A, rfl | rfl⟩ := hermitian_isometry_exhaustion delta h2 g
  · rw [← map_pow]
    exact rho_mem_specialImage_of_domainDeterminant_eq_sq delta h2 _
      (c := domainDeterminant delta A) ((mem_normDeterminantOne delta A.val).mp A.property)
      (map_pow _ _ _)
  · have heq : (rho delta h2 A * gamma delta h2) ^ 2 = rho delta h2 (A * conjugateD delta A) := by
      calc (rho delta h2 A * gamma delta h2) ^ 2 =
          rho delta h2 A * (gamma delta h2 * rho delta h2 A) * gamma delta h2 := by
            simp only [pow_two, mul_assoc]
        _ = rho delta h2 A * (rho delta h2 (conjugateD delta A) * gamma delta h2) *
            gamma delta h2 := by rw [gamma_rho]
        _ = rho delta h2 A * rho delta h2 (conjugateD delta A) *
            (gamma delta h2 * gamma delta h2) := by simp only [mul_assoc]
        _ = _ := by rw [gamma_mul_gamma, mul_one, map_mul]
    rw [heq]
    apply rho_mem_specialImage_of_determinant
    rw [map_mul, domainDeterminant_conjugateD]
    apply Units.ext
    change (domainDeterminant delta A : extension delta) *
      conjugation delta (domainDeterminant delta A : extension delta) = 1
    have hn : QuadraticAlgebra.norm (domainDeterminant delta A : extension delta) = 1 :=
      (mem_normDeterminantOne delta A.val).mp A.property
    rw [extension_norm_product, hn, map_one]

theorem hermitianSpecialImage_quasisimple (h2 : (2 : K) ≠ 0) :
    CFSG.IsQuasisimple (specialImage delta h2) := by
  have hcard := extension_card delta
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension delta) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension delta) ≠ 3 := by
    rw [hcard]
    nlinarith
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension delta) le_rfl
    (Or.inr hE2) (Or.inr hE3)
  rcases quasisimple_homomorphic_images hSL (specialRho delta h2) with h | h
  · exfalso
    have hmem : specialRho delta h2 (unipotentSL (extension delta)) ∈
        (specialRho delta h2).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, specialRho_eq_one_iff] at hmem
    obtain ⟨c, -, hc⟩ := hmem
    exact toGL_unipotentSL_ne_scalar c hc
  · exact h

theorem hermitian_commutator_eq (h2 : (2 : K) ≠ 0) :
    commutator (HermitianIsometries delta) = specialImage delta h2 :=
  commutator_eq_of_isPerfect_of_forall_sq_mem (hermitianSpecialImage_quasisimple delta h2).1
    (hermitian_sq_mem_specialImage delta h2)

end CFSG.LocalAnalysis.ComponentInitial
