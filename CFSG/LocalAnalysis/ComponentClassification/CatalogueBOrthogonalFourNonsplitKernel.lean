module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitReflection

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix

universe u

variable {K : Type u} [Field K] (delta : K) [Fact (¬ IsSquare delta)]

@[expose] def scalarD (c : (extension delta)ˣ)
    (hc : QuadraticAlgebra.norm (c : extension delta) = 1) : normDeterminantOne delta :=
  ⟨GeneralLinearGroup.scalar (Fin 2) c, by
    rw [mem_normDeterminantOne]
    have hs : (GeneralLinearGroup.scalar (Fin 2) c).val.det = (c : extension delta) ^ 2 := by
      rw [GeneralLinearGroup.coe_scalar]
      simp [Matrix.scalar, pow_two]
    rw [hs, map_pow, hc, one_pow]⟩

omit [Fact (¬ IsSquare delta)] in
theorem rho_scalarD (h2 : (2 : K) ≠ 0) (c : (extension delta)ˣ)
    (hc : QuadraticAlgebra.norm (c : extension delta) = 1) :
    rho delta h2 (scalarD delta c hc) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (hermitianCongruence delta (GeneralLinearGroup.scalar (Fin 2) c) X).val = X.val
  rw [hermitianCongruence_scalar, hc, one_smul]

theorem rho_eq_one_iff (h2 : (2 : K) ≠ 0) (A : normDeterminantOne delta) :
    rho delta h2 A = 1 ↔ ∃ c : (extension delta)ˣ,
      QuadraticAlgebra.norm (c : extension delta) = 1 ∧
        A.val = GeneralLinearGroup.scalar (Fin 2) c := by
  constructor
  · intro hA
    have hX : ∀ X : hermitianSubmodule delta,
        A.val.val * X.val * A.val.val.conjTranspose = X.val := fun X => by
      exact congrArg (fun g : HermitianIsometries delta => (g.val X).val) hA
    let I := hermitianCoordinates delta h2 ![1, 1, 0, 0]
    have hI : I.val = (1 : Matrix (Fin 2) (Fin 2) (extension delta)) := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply QuadraticAlgebra.ext <;> simp [I, hermitianCoordinates]
    have hunit : A.val.val * A.val.val.conjTranspose = 1 := by
      simpa only [hI, Matrix.mul_one] using hX I
    have hstar : A.val.val.conjTranspose = A.val⁻¹.val := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) =>
        A.val⁻¹.val * M) hunit
      simpa only [← Matrix.mul_assoc, A.val.inv_mul, Matrix.one_mul, Matrix.mul_one] using hh
    have hcomm : ∀ X : hermitianSubmodule delta, A.val.val * X.val = X.val * A.val.val := by
      intro X
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) =>
        M * A.val.val) (hX X)
      simpa only [hstar, Matrix.mul_assoc, A.val.inv_mul, Matrix.mul_one] using hh
    let P := hermitianCoordinates delta h2 ![1, 0, 0, 0]
    let R := hermitianCoordinates delta h2 ![0, 0, 1, 0]
    have hP : P.val = !![1, 0; 0, 0] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply QuadraticAlgebra.ext <;>
        simp [P, hermitianCoordinates]
    have hR : R.val = !![0, 1; 1, 0] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply QuadraticAlgebra.ext <;>
        simp [R, hermitianCoordinates, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    have hp := hcomm P
    have hr := hcomm R
    rw [hP] at hp
    rw [hR] at hr
    have h01 : A.val.val 0 1 = 0 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) => M 0 1) hp
      simpa [P, hermitianCoordinates, Matrix.mul_apply, Fin.sum_univ_two] using hh.symm
    have h10 : A.val.val 1 0 = 0 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) => M 1 0) hp
      simpa [P, hermitianCoordinates, Matrix.mul_apply, Fin.sum_univ_two] using hh
    have hdiag : A.val.val 0 0 = A.val.val 1 1 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) => M 0 1) hr
      simpa [R, hermitianCoordinates, Matrix.mul_apply, Fin.sum_univ_two] using hh
    have h00 : A.val.val 0 0 ≠ 0 := by
      intro hz
      have hd := congrArg Matrix.det (A.val.mul_inv)
      have hd0 : A.val.val.det = 0 := by
        rw [Matrix.det_fin_two, hz, h01]
        simp
      rw [Matrix.det_mul, hd0, zero_mul, Matrix.det_one] at hd
      exact zero_ne_one hd
    let c : (extension delta)ˣ := Units.mk0 _ h00
    have hscalar : A.val = GeneralLinearGroup.scalar (Fin 2) c := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact h01
      · exact h10
      · exact hdiag.symm
    have hc : QuadraticAlgebra.norm (c : extension delta) = 1 := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) (extension delta) => M 0 0) hunit
      apply (algebraMap K (extension delta)).injective
      rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, map_one]
      simpa [c, Matrix.mul_apply, Fin.sum_univ_two, h01] using hh
    exact ⟨c, hc, hscalar⟩
  · rintro ⟨c, hc, hscalar⟩
    have hAe : A = scalarD delta c hc := Subtype.ext hscalar
    rw [hAe]
    exact rho_scalarD delta h2 c hc

theorem mem_rho_kernel (h2 : (2 : K) ≠ 0) (A : normDeterminantOne delta) :
    A ∈ (rho delta h2).ker ↔ ∃ c : (extension delta)ˣ,
      QuadraticAlgebra.norm (c : extension delta) = 1 ∧
        A.val = GeneralLinearGroup.scalar (Fin 2) c := rho_eq_one_iff delta h2 A

theorem specialRho_eq_one_iff (h2 : (2 : K) ≠ 0)
    (A : SpecialLinearGroup (Fin 2) (extension delta)) :
    specialRho delta h2 A = 1 ↔ ∃ c : (extension delta)ˣ,
      c ^ 2 = 1 ∧ SpecialLinearGroup.toGL A = GeneralLinearGroup.scalar (Fin 2) c := by
  rw [specialRho, MonoidHom.comp_apply, rho_eq_one_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    have hd := congrArg GeneralLinearGroup.det hc
    refine ⟨c, ?_, hc⟩
    simpa [specialMatrices] using hd.symm
  · rintro ⟨c, hc, hA⟩
    have hval : (c : extension delta) ^ 2 = 1 := by exact congrArg Units.val hc
    have hcn : QuadraticAlgebra.norm (c : extension delta) = 1 := by
      have hpm := sq_eq_one_iff.mp hval
      rcases hpm with hc1 | hc1
      · rw [hc1, map_one]
      · rw [hc1, QuadraticAlgebra.norm_neg, map_one]
    exact ⟨c, hcn, hA⟩

theorem specialRho_eq_one_iff_sign (h2 : (2 : K) ≠ 0)
    (A : SpecialLinearGroup (Fin 2) (extension delta)) :
    specialRho delta h2 A = 1 ↔ A = 1 ∨ A = -1 := by
  rw [specialRho_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hA⟩
    have hval : (c : extension delta) ^ 2 = 1 := congrArg Units.val hc
    rcases sq_eq_one_iff.mp hval with hc1 | hc1
    · left
      apply SpecialLinearGroup.toGL_injective
      apply Units.ext
      rw [hA, GeneralLinearGroup.coe_scalar]
      simp [hc1]
    · right
      apply Subtype.ext
      have hh := congrArg Units.val hA
      rw [GeneralLinearGroup.coe_scalar] at hh
      apply Matrix.ext
      intro i j
      have hij := congrFun (congrFun hh i) j
      by_cases h : i = j
      · subst j
        simpa [hc1, Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply] using hij
      · simpa [hc1, Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply, h] using hij
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      apply Units.ext
      apply Matrix.ext
      intro i j
      by_cases h : i = j <;> simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, h]

theorem specialRho_kernel_le_center (h2 : (2 : K) ≠ 0) :
    (specialRho delta h2).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 2) (extension delta)) := by
  intro A hA
  obtain ⟨c, _, hc⟩ := (specialRho_eq_one_iff delta h2 A).mp hA
  apply Subgroup.mem_center_iff.mpr
  intro B
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, hc]
  exact (GeneralLinearGroup.scalar_commute c _).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
