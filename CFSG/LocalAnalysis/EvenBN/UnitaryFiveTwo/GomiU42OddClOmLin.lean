module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmOrd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClOmArith
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClSpArith

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

section ClassI

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem u42_polarBilin_comp_nondeg {Q : QuadraticForm K V} {W : Submodule K V}
    (h : (LinearMap.BilinForm.restrict Q.polarBilin W).Nondegenerate) :
    (Q.comp W.subtype).polarBilin.Nondegenerate := by
  have heq : (Q.comp W.subtype).polarBilin = LinearMap.BilinForm.restrict Q.polarBilin W := by
    rw [QuadraticMap.polarBilin_comp]
    ext x y
    rfl
  rw [heq]
  exact h

theorem u42_omega_classI {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (b : Kˣ) (hb : (c : K) = (b : K) ^ 2) (hpos : (μ : K) / (c : K) = 1)
    (hd : 7 ≤ finrank K V)
    (h1 : 25920 ∣ Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap))
    (h2 : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 414720)
    (h3 : Odd (finrank K V) →
      Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 207360) : False := by
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure
      3 f Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  obtain ⟨hcompl, hne1, hne2, hpos', -⟩ := hsq b hb
  obtain ⟨horth, hnd₁, hnd₂, e, -, -, -⟩ := hpos' hpos
  set V₁ := positiveSquareKernel A (b : K) with hV₁
  set V₂ := negativeSquareKernel A (b : K) with hV₂
  have hnd₁' := u42_polarBilin_comp_nondeg hnd₁
  have hnd₂' := u42_polarBilin_comp_nondeg hnd₂
  have hdimsum : finrank K V₁ + finrank K V₂ = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have ha : 1 ≤ finrank K V₁ := Submodule.one_le_finrank_iff.mpr hne1
  have hb' : 1 ≤ finrank K V₂ := Submodule.one_le_finrank_iff.mpr hne2
  have hcard : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp V₁.subtype)) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp V₂.subtype)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have d₁ := u42_three_pow_dvd_card_orthogonalGroup hf hK hnd₁' rfl ha
  have d₂ := u42_three_pow_dvd_card_orthogonalGroup hf hK hnd₂' rfl hb'
  rcases omega_split_cases hf ha hb' (by omega) with hbig | ⟨hf1, hcases⟩
  · have h5 : 3 ^ 5 ∣ Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
      rw [hcard]
      refine (pow_dvd_pow 3 hbig).trans ?_
      rw [mul_add, pow_add]
      exact Nat.mul_dvd_mul d₁ d₂
    exact not_dvd_414720_of_three_pow_five h5 h2
  · subst hf1
    have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
    rcases hcases with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    ·
      have c1 := u42_card_orthogonalGroup_three_three hK3 hnd₁' hp1
      rcases u42_card_orthogonalGroup_three_four hK3 hnd₂' hp2 with c2 | c2
      · rw [hcard, c1, c2] at h1
        norm_num at h1
      · rw [hcard, c1, c2] at h1
        norm_num at h1
    ·
      have c2 := u42_card_orthogonalGroup_three_three hK3 hnd₂' hp2
      rcases u42_card_orthogonalGroup_three_four hK3 hnd₁' hp1 with c1 | c1
      · rw [hcard, c1, c2] at h1
        norm_num at h1
      · rw [hcard, c1, c2] at h1
        norm_num at h1
    ·
      have c2 := u42_card_orthogonalGroup_three_five hK3 hnd₂' hp2
      have hodd : Odd (finrank K V) := ⟨3, by omega⟩
      have h3' := h3 hodd
      have hle := Nat.le_of_dvd (by norm_num) h3'
      rcases u42_card_orthogonalGroup_three_two hK3 hnd₁' hp1 with c1 | c1
      · rw [hcard, c1, c2] at hle
        norm_num at hle
      · rw [hcard, c1, c2] at hle
        norm_num at hle
    ·
      have c1 := u42_card_orthogonalGroup_three_five hK3 hnd₁' hp1
      have hodd : Odd (finrank K V) := ⟨3, by omega⟩
      have h3' := h3 hodd
      have hle := Nat.le_of_dvd (by norm_num) h3'
      rcases u42_card_orthogonalGroup_three_two hK3 hnd₂' hp2 with c2 | c2
      · rw [hcard, c1, c2] at hle
        norm_num at hle
      · rw [hcard, c1, c2] at hle
        norm_num at hle
    ·
      have hle := Nat.le_of_dvd (by norm_num) h2
      rcases u42_card_orthogonalGroup_three_four hK3 hnd₁' hp1 with c1 | c1 <;>
        rcases u42_card_orthogonalGroup_three_four hK3 hnd₂' hp2 with c2 | c2 <;>
        · rw [hcard, c1, c2] at hle
          norm_num at hle

end ClassI

section ClassII

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem u42_omega_classII {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (b : Kˣ) (hb : (c : K) = (b : K) ^ 2) (hneg : (μ : K) / (c : K) = -1)
    (hd : 7 ≤ finrank K V)
    (h2 : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 414720) : False := by
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure
      3 f Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  obtain ⟨hcompl, -, -, -, hneg'⟩ := hsq b hb
  obtain ⟨-, -, -, hdeq, -, -, e, dual, -, -, -, -⟩ := hneg' hneg
  have hdimsum : finrank K (positiveSquareKernel A (b : K)) +
      finrank K (negativeSquareKernel A (b : K)) = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hm : 4 ≤ finrank K (positiveSquareKernel A (b : K)) := by omega
  let eGL := e.trans (CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Module.finBasis K (positiveSquareKernel A (b : K))))
  have hcard : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) =
      Nat.card (GL (Fin (finrank K (positiveSquareKernel A (b : K)))) K) :=
    Nat.card_congr eGL.toEquiv
  have h5 : 3 ^ 5 ∣ Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
    rw [hcard]
    exact (pow_dvd_pow 3 (u42_class_gl_numeric hf hm)).trans (three_pow_dvd_card_GL hK)
  exact not_dvd_414720_of_three_pow_five h5 h2

end ClassII

section ClassNonsquare

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem u42_omega_classIII {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hsq : ¬ IsSquare (c : K)) (hpos : (μ : K) / (c : K) = 1) (hd : 7 ≤ finrank K V)
    (h2 : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 414720) : False := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A c hsquare
  let := scalarField A.toLinearMap c hsq hs
  let := evaluationModule A.toLinearMap
  let := scalarAlgebra_finite_type A.toLinearMap c hsq hs
  let := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = 3 ^ (2 * f) := by
    rw [scalarAlgebra_card A.toLinearMap c hsq hs, hK, ← pow_mul, mul_comm]
  have hdimE : finrank K V = 2 * finrank (scalarAlgebra A.toLinearMap) V :=
    evaluationModule_finrank A.toLinearMap c hsq hs
  have hadj := positive_square_adjoint Q A c μ c.ne_zero hsquare hsim hpos
  have hnd := actualPositiveQuadratic_nondegenerate Q A.toLinearMap c c.ne_zero hsq hs hadj hQ h2'
  have hcard := Nat.card_congr
    (actualPositiveCentralizerEquiv Q A.toLinearMap c c.ne_zero hsq hs hadj h2').toEquiv
  have hm : 4 ≤ finrank (scalarAlgebra A.toLinearMap) V := by omega
  have d3 := u42_three_pow_dvd_card_orthogonalGroup (K := scalarAlgebra A.toLinearMap) (W := V)
    (f := 2 * f) (by omega) hE hnd rfl (by omega)
  rw [← hcard] at d3
  rcases u42_class_three_numeric hf hm with hbig | ⟨hm4, hf1⟩
  · exact not_dvd_414720_of_three_pow_five ((pow_dvd_pow 3 hbig).trans d3) h2
  · subst hf1
    have hE9 : Nat.card (scalarAlgebra A.toLinearMap) = 9 := by rw [hE]; norm_num
    have hgt := u42_card_orthogonalGroup_nine_four (K := scalarAlgebra A.toLinearMap) (W := V)
      hE9 hnd hm4
    rw [← hcard] at hgt
    exact false_of_bounds_omega h2 hgt

theorem u42_omega_classIV {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hsq : ¬ IsSquare (c : K)) (hneg : (μ : K) / (c : K) = -1) (hd : 7 ≤ finrank K V)
    (h2 : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 414720) : False := by
  have hodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2' := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A c hsquare
  let := scalarField A.toLinearMap c hsq hs
  let := evaluationModule A.toLinearMap
  let := scalarAlgebra_finite_type A.toLinearMap c hsq hs
  let := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = (3 ^ f) ^ 2 := by
    rw [scalarAlgebra_card A.toLinearMap c hsq hs, hK]
  have hdimE : finrank K V = 2 * finrank (scalarAlgebra A.toLinearMap) V :=
    evaluationModule_finrank A.toLinearMap c hsq hs
  have hadj := negative_square_adjoint Q A c μ c.ne_zero hsquare hsim hneg
  have hpow : ∀ z, (conjugation A.toLinearMap c hsq hs).toRingEquiv z = z ^ (3 ^ f) := by
    intro z
    rw [← hK]
    exact conjugation_eq_card_power A.toLinearMap c hsq hs h2' z
  have hcard := Nat.card_congr
    (actualNegativeCentralizerEquiv Q A.toLinearMap c c.ne_zero hsq hs hadj h2').toEquiv
  have hm : 4 ≤ finrank (scalarAlgebra A.toLinearMap) V := by omega
  have d3 := u42_three_pow_dvd_card_unitary (E := scalarAlgebra A.toLinearMap) (W := V)
    (sigma := (conjugation A.toLinearMap c hsq hs).toRingEquiv) (f := f) hf hE rfl (by omega) _
    (actualNegativeHermitian_isSymm Q A.toLinearMap c c.ne_zero hsq hs hadj)
    (actualNegativeHermitian_nondegenerate Q A.toLinearMap c c.ne_zero hsq hs hadj hQ) hpow
  rw [← hcard] at d3
  exact not_dvd_414720_of_three_pow_five
    ((pow_dvd_pow 3 (u42_class_gl_numeric hf hm)).trans d3) h2

end ClassNonsquare

section Core

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem u42_omega_linear_false {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (c μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (c : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ a : K, A.toLinearMap ≠ a • (1 : Module.End K V))
    (hd : 7 ≤ finrank K V)
    (h1 : 25920 ∣ Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap))
    (h2 : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 414720)
    (h3 : Odd (finrank K V) →
      Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) ∣ 207360) : False := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hsign, -, -, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure
      3 f Nat.prime_three (by norm_num) hf hK (by omega) Q hQ A c μ hsquare hsim hnonscalar
  by_cases hsqc : IsSquare (c : K)
  · obtain ⟨r, hr⟩ := hsqc
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa using hr)
    let b : Kˣ := Units.mk0 r hr0
    have hb : (c : K) = (b : K) ^ 2 := by rw [hr, sq]; rfl
    rcases hsign with hpos | hneg
    · exact u42_omega_classI hf hK Q hQ A c μ hsquare hsim hnonscalar b hb hpos hd h1 h2 h3
    · exact u42_omega_classII hf hK Q hQ A c μ hsquare hsim hnonscalar b hb hneg hd h2
  · rcases hsign with hpos | hneg
    · exact u42_omega_classIII hf hK Q hQ A c μ hsquare hsim hsqc hpos hd h2
    · exact u42_omega_classIV hf hK Q hQ A c μ hsquare hsim hsqc hneg hd h2

end Core

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
