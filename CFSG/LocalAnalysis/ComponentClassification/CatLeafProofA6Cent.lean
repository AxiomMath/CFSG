module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Orth2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Module

theorem a6CentreForm_unitary_pos
    {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 1 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e)) :
    A6CentreForm (CatalogueBUnitaryIsometry.isometryGroup h) := by
  rcases Nat.lt_or_ge (finrank E W) 2 with h1 | h2
  · have := CatalogueBUnitaryIsometry.isometry_one_solvable h (by omega)
    exact a6CentreForm_of_isSolvable
  · exact a6CentreForm_unitary hℓ hℓ2 he hE h2 h hsym hnd hsigma hne hsig

section GeneralLinear

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem a6CentreForm_glCentralizer
    {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (A : GL (Fin n) K) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1) (lambda : Kˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) lambda) :
    A6CentreForm (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, -, hr, hs, -, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A lambda h2
        hne hsq hsquare
    exact a6CentreForm_of_mulEquiv e
      (a6CentreForm_prod (a6CentreForm_GL hp hp2 hf hK hr) (a6CentreForm_GL hp hp2 hf hK hs))
  · let : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    exact a6CentreForm_of_mulEquiv
      (CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq)
      (a6CentreForm_GL hp hp2 (j := 2 * f) (by omega)
        (by rw [OddInner.card_extension, hK, ← pow_mul, mul_comm]) hm)
end GeneralLinear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem a6CentreForm_sesqCentralizer
    {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) :
    A6CentreForm (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, -, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  obtain ⟨hsig2, hsig1, -⟩ :=
    CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, -⟩ := hsplit hN
    have := Finite.of_equiv _ (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h
      (B.domRestrict₁₂ (eigenPlus l (unitaryOp A)) (eigenPlus l (unitaryOp A)))).toEquiv
    have := Finite.of_equiv _ (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h
      (B.domRestrict₁₂ (eigenMinus l (unitaryOp A)) (eigenMinus l (unitaryOp A)))).toEquiv
    exact a6CentreForm_of_mulEquiv
      (e.trans (MulEquiv.prodCongr (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)
        (CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h _)))
      (fun M hMc => a6CentreForm_prod
        (fun M₁ hM₁ => a6CentreForm_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hP) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlP) hsig2 hsig1 hsig M₁ hM₁)
        (fun M₂ hM₂ => a6CentreForm_unitary_pos h.prime hp h.one_le h.card_eq_sq
          (Submodule.one_le_finrank_iff.mpr hM) _ (hsymm _)
          (CatalogueBUnitaryB.nondegenerate_of_isSymm (hsymm _) hlM) hsig2 hsig1 hsig M₂ hM₂)
        M hMc)
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    exact a6CentreForm_of_mulEquiv
      (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv))
      (a6CentreForm_GL h.prime hp (j := 2 * f) (by have := h.one_le; omega) h.card
        (by omega))
end Unitary

section Orthogonal

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

theorem a6CentreForm_orthogonalOperatorCentralizer
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    A6CentreForm (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hsign := original_similarity_ratio_sign Q hQ A d μ d.ne_zero hsquare hsim
  by_cases hsq : IsSquare (d : K)
  · obtain ⟨b, hroot⟩ := hsq.exists_sq
    have hb : b ≠ 0 := by
      intro hb
      apply d.ne_zero
      simp [hroot, hb]
    rcases hsign with hpos | hneg
    ·
      have hnd := positive_square_kernel_nondegenerate Q hQ A d μ b d.ne_zero hb h2
        hsquare hroot hsim hpos
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
      exact a6CentreForm_of_mulEquiv
        (positiveSquareKernelCentralizerEquiv Q A d μ b d.ne_zero hb h2 hsquare hroot hsim hpos)
        (a6CentreForm_prod (a6CentreForm_orthogonal hp hp2 hf hK _ hndplus)
          (a6CentreForm_orthogonal hp hp2 hf hK _ hndminus))
    ·
      have hn := (square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar).1
      have hdim : 1 ≤ finrank K (positiveSquareKernel A b) := by
        by_contra h
        exact hn (Submodule.finrank_eq_zero.mp (by omega))
      exact a6CentreForm_of_mulEquiv
        ((negativeSquareKernelCentralizerEquiv Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
          hneg).trans (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K _)))
        (a6CentreForm_GL hp hp2 hf hK hdim)
  · have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
    let := scalarField A.toLinearMap d hsq hs
    let := evaluationModule A.toLinearMap
    let := scalarAlgebra_finite_type A.toLinearMap d hsq hs
    let := evaluationModule_finite A.toLinearMap
    have hE : Nat.card (scalarAlgebra A.toLinearMap) = (p ^ f) ^ 2 := by
      rw [scalarAlgebra_card A.toLinearMap d hsq hs, hK]
    have hW : 1 ≤ finrank (scalarAlgebra A.toLinearMap) V := by
      have := Module.finrank_pos (R := scalarAlgebra A.toLinearMap) (M := V)
      omega
    rcases hsign with hpos | hneg
    ·
      have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hpos
      exact a6CentreForm_of_mulEquiv
        (actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2)
        (a6CentreForm_orthogonal hp hp2 (e := 2 * f) (by omega)
          (by rw [hE, ← pow_mul, mul_comm]) _
          (actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ h2))
    ·
      have hadj := negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hneg
      have hsig : (conjugation A.toLinearMap d hsq hs).toRingEquiv ^ 2 = 1 := by
        apply RingEquiv.ext
        intro z
        change conjugation A.toLinearMap d hsq hs (conjugation A.toLinearMap d hsq hs z) = z
        exact conjugation_involutive A.toLinearMap d hsq hs z
      have hne : (conjugation A.toLinearMap d hsq hs).toRingEquiv ≠ 1 := by
        intro heq
        apply conjugation_ne_one A.toLinearMap d hsq hs h2
        apply AlgEquiv.ext
        intro z
        exact congrArg (fun s : scalarAlgebra A.toLinearMap ≃+* scalarAlgebra A.toLinearMap =>
          s z) heq
      have hpow : ∀ z, (conjugation A.toLinearMap d hsq hs).toRingEquiv z = z ^ (p ^ f) := by
        intro z
        rw [← hK]
        exact conjugation_eq_card_power A.toLinearMap d hsq hs h2 z
      exact a6CentreForm_of_mulEquiv
        (actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2)
        (a6CentreForm_unitary_pos hp hp2 hf hE hW _
          (actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hsq hs hadj)
          (actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ)
          hsig hne hpow)
end Orthogonal

end CFSG.ComponentClassification.CatLeafProof
