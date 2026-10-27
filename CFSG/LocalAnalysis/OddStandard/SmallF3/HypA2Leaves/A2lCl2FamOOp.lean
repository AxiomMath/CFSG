module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamUCent

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof.OddInner
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup Module
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

theorem cl24_oddLie_orthogonalOperatorCentralizer {p f : ℕ} (hO : Cl24OrthComp p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    {L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap)} (hL : IsComponent L)
    {Rel : ℕ → Prop}
    (hRel : ∀ f', f' = f ∨ f' = 2 * f ∨ (finrank K V = 8 ∧ f' = 4 * f) → Rel f' := by cl24_rel) :
    Cl24Q p Rel L := by
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
      exact cl24_of_component_equiv
        (positiveSquareKernelCentralizerEquiv Q A d μ b d.ne_zero hb h2 hsquare hroot hsim hpos)
        (fun M hM => cl24_prod
          (fun M₁ hM₁ => cl24_oddLie_orthogonal hO hp hp2 hf hK _ hndplus hM₁)
          (fun M₂ hM₂ => cl24_oddLie_orthogonal hO hp hp2 hf hK _ hndminus hM₂) hM) hL
    ·
      have hn := (square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar).1
      have hdim : 1 ≤ finrank K (positiveSquareKernel A b) := by
        by_contra h
        exact hn (Submodule.finrank_eq_zero.mp (by omega))
      exact cl24_of_component_equiv
        ((negativeSquareKernelCentralizerEquiv Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
          hneg).trans (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K _)))
        (fun M hM => cl24_oddLie_GL hp hf hK hdim hM) hL
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
    have hdimE : finrank K V = 2 * finrank (scalarAlgebra A.toLinearMap) V := by
      have h1 := Module.natCard_eq_pow_finrank (K := K) (V := V)
      have h2' := Module.natCard_eq_pow_finrank (K := scalarAlgebra A.toLinearMap) (V := V)
      rw [hE, ← pow_mul] at h2'
      rw [hK] at h1
      exact Nat.pow_right_injective (le_trans hp.two_le (Nat.le_self_pow (by omega) p))
        (h1.symm.trans h2')
    rcases hsign with hpos | hneg
    ·
      have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hpos
      exact cl24_of_component_equiv
        (actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2)
        (fun M hM => cl24_oddLie_orthogonal hO hp hp2 (e := 2 * f) (by omega)
          (by rw [hE, ← pow_mul, mul_comm]) _
          (actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ h2)
          hM (hRel := fun f' h' => hRel f' (by rcases h' with h' | ⟨h4, h'⟩ <;> omega))) hL
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
      exact cl24_of_component_equiv
        (actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2)
        (fun M hM => cl24_oddLie_unitary_pos hp hp2 hf hE hW _
          (actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hsq hs hadj)
          (actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ)
          hsig hne hpow hM) hL

end CFSG.OddStandard.SmallF3.HypA2Leaves
