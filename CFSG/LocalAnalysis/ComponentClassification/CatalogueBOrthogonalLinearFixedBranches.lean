module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssemblyAllDimensions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureNonsquare

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

open CatalogueBOrthogonalScalarSquare CatalogueBOrthogonalScalarSquareField
  CatalogueBOrthogonalScalarSquareForms

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem original_generalLinear_pComponent_quasisimple
    (hn : 1 ≤ Module.finrank K V) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (V ≃ₗ[K] V)) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let b := Module.finBasis K V
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (CatalogueBAlternatingIsometry.basisMatrixEquiv b)
    (CatalogueBGeneralLinear.pComponent_quasisimple (Module.finrank K V) K hn p) L hL

theorem positive_square_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ b : K) (hd : d ≠ 0) (hb : b ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hpositive : μ / d = 1) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hnd := positive_square_kernel_nondegenerate Q hQ A d μ b hd hb h2
    hsquare hroot hsim hpositive
  have hndplus : (Q.comp (positiveSquareKernel A b).subtype).polarBilin.Nondegenerate := by
    have heq : (Q.comp (positiveSquareKernel A b).subtype).polarBilin =
        LinearMap.BilinForm.restrict Q.polarBilin (positiveSquareKernel A b) := by
      rw [QuadraticMap.polarBilin_comp]
      ext x y
      rfl
    rw [heq]
    exact hnd.1
  have hndminus : (Q.comp (negativeSquareKernel A b).subtype).polarBilin.Nondegenerate := by
    have heq : (Q.comp (negativeSquareKernel A b).subtype).polarBilin =
        LinearMap.BilinForm.restrict Q.polarBilin (negativeSquareKernel A b) := by
      rw [QuadraticMap.polarBilin_comp]
      ext x y
      rfl
    rw [heq]
    exact hnd.2
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (positiveSquareKernelCentralizerEquiv Q A d μ b hd hb h2 hsquare hroot hsim hpositive)
    (CatalogueBProjectiveInvolutionProduct.pComponent_quasisimple_product p
      (CatalogueBOrthogonalAssembly.orthogonal_all_dimensional_pComponent_quasisimple hodd _ hndplus p)
      (CatalogueBOrthogonalAssembly.orthogonal_all_dimensional_pComponent_quasisimple hodd _ hndminus p))
    L hL

theorem negative_square_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ b : K) (hd : d ≠ 0) (hb : b ≠ 0)
    (hsquare : ∀ x : V, A (A x) = d • x) (hroot : d = b ^ 2)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (hnegative : μ / d = -1) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hn := (square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar).1
  have hdim : 1 ≤ Module.finrank K (positiveSquareKernel A b) := by
    by_contra h
    exact hn (Submodule.finrank_eq_zero.mp (by omega))
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (negativeSquareKernelCentralizerEquiv Q hQ A d μ b hd hb h2 hsquare hroot hsim hnegative)
    (original_generalLinear_pComponent_quasisimple hdim p) L hL

variable [Nontrivial V]

theorem positive_nonsquare_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y))
    (p : ℕ) [Fact p.Prime] (L : Subgroup (orthogonalOperatorCentralizer Q T))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := scalarAlgebra_finite_type T d hns hsquare
  let := evaluationModule_finite T
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hEodd : Odd (Nat.card (scalarAlgebra T)) := by
    rw [scalarAlgebra_card T d hns hsquare]
    exact hodd.pow
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (actualPositiveCentralizerEquiv Q T d hd hns hsquare hadj h2)
    (CatalogueBOrthogonalAssembly.orthogonal_all_dimensional_pComponent_quasisimple hEodd _
      (actualPositiveQuadratic_nondegenerate Q T d hd hns hsquare hadj hQ h2) p) L hL

@[expose] def scalarFixedFieldEquiv (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    K ≃+* CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
      (conjugation T d hns hsquare).toRingEquiv := by
  let := scalarField T d hns hsquare
  let F := CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
    (conjugation T d hns hsquare).toRingEquiv
  let j : K →+* F := (algebraMap K (scalarAlgebra T)).codRestrict F (fun a =>
    (CatalogueBLinearTwoDescent.mem_fixedSubfield _ _ _).mpr
      ((conjugation T d hns hsquare).commutes a))
  apply RingEquiv.ofBijective j
  constructor
  · intro a b hab
    exact (algebraMap K (scalarAlgebra T)).injective (congrArg Subtype.val hab)
  · intro z
    obtain ⟨a, ha⟩ := (conjugation_fixed_iff T d hns hsquare h2 z.val).mp
      ((CatalogueBLinearTwoDescent.mem_fixedSubfield _ _ _).mp z.property)
    exact ⟨a, Subtype.ext ha.symm⟩

omit [Finite K] [FiniteDimensional K V] in
theorem scalarFixedField_card (T : Module.End K V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (h2 : (2 : K) ≠ 0) :
    letI := scalarField T d hns hsquare
    Nat.card (CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
      (conjugation T d hns hsquare).toRingEquiv) = Nat.card K := by
  let := scalarField T d hns hsquare
  exact Nat.card_congr (scalarFixedFieldEquiv T d hns hsquare h2).symm.toEquiv

theorem negative_nonsquare_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Module.End K V) (d : K) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d)
    (hadj : ∀ x y, Q.polarBilin (T x) y = -Q.polarBilin x (T y))
    (p : ℕ) [Fact p.Prime] (L : Subgroup (orthogonalOperatorCentralizer Q T))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  let := scalarAlgebra_finite_type T d hns hsquare
  let := evaluationModule_finite T
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let h := actualNegativeHermitian Q.polarBilin T d hd hns hsquare hadj
  have hsig : (conjugation T d hns hsquare).toRingEquiv ^ 2 = 1 := by
    apply RingEquiv.ext
    intro z
    change conjugation T d hns hsquare (conjugation T d hns hsquare z) = z
    exact conjugation_involutive T d hns hsquare z
  have hne : (conjugation T d hns hsquare).toRingEquiv ≠ 1 := by
    intro heq
    apply conjugation_ne_one T d hns hsquare h2
    apply AlgEquiv.ext
    intro z
    exact congrArg (fun s : scalarAlgebra T ≃+* scalarAlgebra T => s z) heq
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield (scalarAlgebra T)
      (conjugation T d hns hsquare).toRingEquiv) ≠ 2 := by
    rw [scalarFixedField_card T d hns hsquare h2]
    intro heq
    have hh := hodd
    rw [heq] at hh
    norm_num at hh
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (actualNegativeCentralizerEquiv Q T d hd hns hsquare hadj h2)
    (CatalogueBUnitaryIsometry.isometry_all_dimensions_pComponent_quasisimple h
      (actualNegativeHermitian_isSymm Q T d hd hns hsquare hadj)
      (actualNegativeHermitian_nondegenerate Q T d hd hns hsquare hadj hQ)
      hsig hne (by have := Module.finrank_pos (R := scalarAlgebra T) (M := V); omega)
      hq2 p (Fact.out : p.Prime)) L hL

theorem scalar_square_centralizer_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hsign := original_similarity_ratio_sign Q hQ A d μ d.ne_zero hsquare hsim
  by_cases hsq : IsSquare (d : K)
  · obtain ⟨b, hroot⟩ := hsq.exists_sq
    have hb : b ≠ 0 := by intro hb; apply d.ne_zero; simp [hroot, hb]
    rcases hsign with hp | hm
    · exact positive_square_pComponent_quasisimple hodd Q hQ A d μ b d.ne_zero hb
        hsquare hroot hsim hp p L hL
    · exact negative_square_pComponent_quasisimple hodd Q hQ A d μ b d.ne_zero hb
        hsquare hroot hsim hnonscalar hm p L hL
  · have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
    rcases hsign with hp | hm
    · exact positive_nonsquare_pComponent_quasisimple hodd Q hQ A.toLinearMap d d.ne_zero hsq hs
        (positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hp) p L hL
    · exact negative_nonsquare_pComponent_quasisimple hodd Q hQ A.toLinearMap d d.ne_zero hsq hs
        (negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hm) p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
