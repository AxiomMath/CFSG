module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5OmegaProd

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Omega

open CFSG Subgroup Module CFSG.Open
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.CatLeafProof.X10Sp (centralModel_unitary_component)
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL (eq_psl_two_one_of_a5)
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

theorem notOnlyA5_orthogonalOperatorCentralizer {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 5 ^ f) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hd : 7 ≤ Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    NotOnlyA5 ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (Nat.prime_five.odd_of_ne_two (by norm_num)).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hsign, -, hsq, hnsq⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure 5 f
      Nat.prime_five (by norm_num) hf hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  by_cases hsqd : IsSquare (d : K)
  ·
    obtain ⟨r, hr⟩ := hsqd
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact d.ne_zero (by simpa using hr)
    obtain ⟨b, hb⟩ : ∃ b : Kˣ, (d : K) = (b : K) ^ 2 :=
      ⟨Units.mk0 r hr0, by rw [hr, sq]; rfl⟩
    obtain ⟨hcompl, -, -, hpos, hneg⟩ := hsq b hb
    rcases hsign with hp | hn
    ·
      obtain ⟨-, hnd₁, hnd₂, e, -⟩ := hpos hp
      have hQ₁ : (Q.comp (positiveSquareKernel A (b : K)).subtype).polarBilin.Nondegenerate := by
        rw [QuadraticMap.polarBilin_comp]
        exact hnd₁
      have hQ₂ : (Q.comp (negativeSquareKernel A (b : K)).subtype).polarBilin.Nondegenerate := by
        rw [QuadraticMap.polarBilin_comp]
        exact hnd₂
      have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
      exact NotOnlyA5.of_mulEquiv e (notOnlyA5_orth_prod hf hK _ hQ₁ _ hQ₂ (by omega))
    ·
      obtain ⟨-, -, -, -, hdimP, -, e, -⟩ := hneg hn
      refine NotOnlyA5.of_mulEquiv (e.trans (CatalogueBAlternatingIsometry.basisMatrixEquiv
        (Module.finBasis K (positiveSquareKernel A (b : K))))) ?_
      intro L hL hA
      exfalso
      have hmodel := centralModel_GL_component_two_le Nat.prime_five (by norm_num) hf hK
        (by omega) (Or.inl (by omega)) hL
      obtain ⟨-, hm2, -⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hmodel.1 hmodel.2 hA
      omega
  ·
    have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
    letI := scalarField A.toLinearMap d hsqd hs
    letI := evaluationModule A.toLinearMap
    haveI := scalarAlgebra_finite_type A.toLinearMap d hsqd hs
    haveI := evaluationModule_finite A.toLinearMap
    have hE : Nat.card (scalarAlgebra A.toLinearMap) = (5 ^ f) ^ 2 := by
      rw [scalarAlgebra_card A.toLinearMap d hsqd hs, hK]
    have hdimE := evaluationModule_finrank A.toLinearMap d hsqd hs
    rcases hsign with hp | hn
    ·
      have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hp
      refine NotOnlyA5.of_mulEquiv
        (actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hsqd hs hadj h2) ?_
      intro L hL hA
      exfalso
      have hmodel := orthogonal_component_models Nat.prime_five (by norm_num) (e := 2 * f)
        (by omega) (by rw [hE, ← pow_mul, mul_comm]) _
        (actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hsqd hs hadj hQ h2)
        (by omega) hL
      obtain ⟨-, he⟩ := le_four_of_modelIn_orthTuples hmodel hA
      omega
    ·
      have hadj := negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hn
      have hsig : (conjugation A.toLinearMap d hsqd hs).toRingEquiv ^ 2 = 1 := by
        apply RingEquiv.ext
        intro z
        change conjugation A.toLinearMap d hsqd hs (conjugation A.toLinearMap d hsqd hs z) = z
        exact conjugation_involutive A.toLinearMap d hsqd hs z
      have hne : (conjugation A.toLinearMap d hsqd hs).toRingEquiv ≠ 1 := by
        intro heq
        apply conjugation_ne_one A.toLinearMap d hsqd hs h2
        apply AlgEquiv.ext
        intro z
        exact congrArg (fun s : scalarAlgebra A.toLinearMap ≃+* scalarAlgebra A.toLinearMap =>
          s z) heq
      have hpow : ∀ z, (conjugation A.toLinearMap d hsqd hs).toRingEquiv z = z ^ (5 ^ f) := by
        intro z
        rw [← hK]
        exact conjugation_eq_card_power A.toLinearMap d hsqd hs h2 z
      refine NotOnlyA5.of_mulEquiv
        (actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hsqd hs hadj h2) ?_
      intro L hL hA
      exfalso
      have hmodel := centralModel_unitary_component Nat.prime_five (by norm_num) hf hE
        (by omega) _ (actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hsqd hs hadj)
        (actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hsqd hs hadj hQ)
        hsig hne hpow hL
      obtain ⟨h1, -, -⟩ := eq_psl_two_one_of_a5 (Or.inr (Or.inl rfl)) hmodel.1 hmodel.2 hA
      exact absurd h1 (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.C5Omega
