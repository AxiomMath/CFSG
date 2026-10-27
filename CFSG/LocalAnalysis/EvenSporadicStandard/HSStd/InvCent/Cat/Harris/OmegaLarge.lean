module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Props
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmall

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Module Subgroup
open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatFC CFSG.ComponentClassification.CatFC.OmegaSmall

theorem omegaLb_mul_gt_big {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = 7 ∨ a + b = 8) :
    11520 < omegaLb a * omegaLb b := by
  have ha7 : a ≤ 7 := by omega
  have hb7 : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

section Cases

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_cent_split_big {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (b : K) (hb : b ≠ 0) (hroot : (d : K) = b ^ 2) (hpos : (μ : K) / (d : K) = 1) :
    11520 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hnd := positive_square_kernel_nondegenerate Q hQ A d μ b d.ne_zero hb h2 hsquare hroot
    hsim hpos
  have hcompl := square_kernels_isCompl A d b hb h2 hsquare hroot
  have hne := square_kernels_ne_bot A d b hb h2 hsquare hroot hnonscalar
  let e := positiveSquareKernelCentralizerEquiv Q A d μ b d.ne_zero hb h2 hsquare hroot hsim hpos
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
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  have hp1 : 1 ≤ finrank K (positiveSquareKernel A b) := Submodule.one_le_finrank_iff.mpr hne.1
  have hm1 : 1 ≤ finrank K (negativeSquareKernel A b) := Submodule.one_le_finrank_iff.mpr hne.2
  have hb1 := omega_card_orthogonalGroup_ge hK hndplus hp1 (by omega) rfl
  have hb2 := omega_card_orthogonalGroup_ge hK hndminus hm1 (by omega) rfl
  have hcard : Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (positiveSquareKernel A b).subtype)) *
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (negativeSquareKernel A b).subtype)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  rw [hcard]
  exact lt_of_lt_of_le (omegaLb_mul_gt_big hp1 hm1 (by omega)) (Nat.mul_le_mul hb1 hb2)

theorem omega_cent_paired_big {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (b : K) (hb : b ≠ 0) (hroot : (d : K) = b ^ 2) (hneg : (μ : K) / (d : K) = -1) :
    11520 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hcompl := square_kernels_isCompl A d b hb h2 hsquare hroot
  have hgeom := negative_square_kernel_geometry Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
    hneg
  let e := negativeSquareKernelCentralizerEquiv Q hQ A d μ b d.ne_zero hb h2 hsquare hroot hsim
    hneg
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  obtain ⟨-, -, -, -, hh1, hh2⟩ := hgeom
  have hfr : finrank K (positiveSquareKernel A b) = 4 := by omega
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartOne.LIT.card_linearEquiv_eq 4 hfr, hK]
  decide

end Cases

section Field

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem omega_cent_field_pos_big {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ¬ IsSquare (d : K)) (hpos : (μ : K) / (d : K) = 1) :
    11520 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
  letI := scalarField A.toLinearMap d hns hs
  letI := evaluationModule A.toLinearMap
  haveI : Finite (scalarAlgebra A.toLinearMap) := scalarAlgebra_finite_type A.toLinearMap d hns hs
  haveI : Module.Finite (scalarAlgebra A.toLinearMap) V := evaluationModule_finite A.toLinearMap
  have hE : ((Nat.card (scalarAlgebra A.toLinearMap) : ℕ) : ℤ) = 9 := by
    rw [scalarAlgebra_card A.toLinearMap d hns hs, hK]; norm_num
  have hfr := evaluationModule_finrank A.toLinearMap d hns hs
  have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hpos
  have hnd := actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hns hs hadj hQ h2
  let e := actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hns hs hadj h2
  rw [Nat.card_congr e.toEquiv]
  have hfr4 : finrank (scalarAlgebra A.toLinearMap) V = 2 * (1 + 1) := by omega
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType
      (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) ∨
      (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) := by
    by_cases hP : CFSG.GroupTheory.WeirSylow.IsPlusType
      (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)
    · exact ⟨1, Or.inl ⟨rfl, hP⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, hP⟩⟩
  have hε' : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (K := scalarAlgebra A.toLinearMap) hnd (m := 1) hfr4 hε
  rw [hE] at h
  generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup
    (actualPositiveQuadratic Q A.toLinearMap d d.ne_zero hns hs hadj)) = c at h ⊢
  rcases hε' with rfl | rfl <;> (norm_num [Finset.prod_Icc_succ_top] at h; omega)

theorem omega_cent_field_neg_big {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hns : ¬ IsSquare (d : K)) (hneg : (μ : K) / (d : K) = -1) :
    11520 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK)
  have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
  letI := scalarField A.toLinearMap d hns hs
  letI := evaluationModule A.toLinearMap
  haveI : Finite (scalarAlgebra A.toLinearMap) := scalarAlgebra_finite_type A.toLinearMap d hns hs
  haveI : Module.Finite (scalarAlgebra A.toLinearMap) V := evaluationModule_finite A.toLinearMap
  have hE : Nat.card (scalarAlgebra A.toLinearMap) = (3 ^ 1) ^ 2 := by
    rw [scalarAlgebra_card A.toLinearMap d hns hs, hK]; norm_num
  have hfr := evaluationModule_finrank A.toLinearMap d hns hs
  have hadj := negative_square_adjoint Q A d μ d.ne_zero hsquare hsim hneg
  have hsymm := actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hns hs hadj
  have hnd := actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hns hs hadj hQ
  let e := actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hns hs hadj h2
  rw [Nat.card_congr e.toEquiv]
  have hfr4 : finrank (scalarAlgebra A.toLinearMap) V = 4 := by omega
  have h := card_isometryGroup_unitary (sigma := (conjugation A.toLinearMap d hns hs).toRingEquiv)
    Nat.prime_three le_rfl hE
    (actualNegativeHermitian Q.polarBilin A.toLinearMap d d.ne_zero hns hs hadj) hsymm hnd
    (fun z => by
      have := finite_conjugation_eq_card_power A.toLinearMap d hns hs z
      rw [hK] at this
      simpa using this) hfr4 (by norm_num)
  generalize Nat.card (CatalogueBUnitaryIsometry.isometryGroup
    (actualNegativeHermitian Q.polarBilin A.toLinearMap d d.ne_zero hns hs hadj)) = c at h ⊢
  norm_num [Finset.prod_Icc_succ_top] at h
  omega

theorem omega_centralizer_card_gt_big {n : ℕ} (hK : Nat.card K = 3) (hn : finrank K V = n)
    (hn78 : n = 7 ∨ n = 8) (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    11520 < Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsign := original_similarity_ratio_sign Q hQ A d μ
    d.ne_zero hsquare hsim
  by_cases hsq : IsSquare (d : K)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      intro h0
      apply d.ne_zero
      rw [hr, h0, mul_zero]
    have hroot : (d : K) = r ^ 2 := by rw [hr]; ring
    rcases hsign with h1 | h1
    · exact omega_cent_split_big hK hn hn78 Q hQ A d μ hsquare hsim hnonscalar r hr0 hroot h1
    · exact omega_cent_paired_big hK hn hn78 Q hQ A d μ hsquare hsim hnonscalar r hr0 hroot h1
  · rcases hsign with h1 | h1
    · exact omega_cent_field_pos_big hK hn hn78 Q hQ A d μ hsquare hsim hsq h1
    · exact omega_cent_field_neg_big hK hn hn78 Q hQ A d μ hsquare hsim hsq h1

end Field

section Involution

variable {K : Type} [Field K] [Finite K]

theorem omega_fixed_card_gt_big (hK : Nat.card K = 3) {d : ℕ} (hd : d = 7 ∨ d = 8)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      4 * Nat.card (matrixProjectiveDerived Q))
    (σ : MulAut (matrixProjectiveDerived Q)) (hσ : orderOf σ = 2) :
    2880 < Nat.card (fixedSubgroup σ) := by
  have h2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    rw [← pow_two]
    exact h
  have h1 : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨β, g, hg, hσ2, ⟨c, hc⟩, hns, hfield⟩ := hrep.2 σ h2 h1
  have hg1 : g.val.right = 1 := by
    by_contra hne
    obtain ⟨hcardK, -⟩ := hfield hne
    rw [hK] at hcardK
    rcases Nat.lt_or_ge (Nat.card {c : K // g.val.right c = c}) 2 with hm | hm
    · interval_cases (Nat.card {c : K // g.val.right c = c}) <;> omega
    · nlinarith
  have hcongr : Nat.card (fixedSubgroup σ) =
      Nat.card (fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
    have : MulAut.congr β⁻¹ σ = matrixProjectiveConjugationHom Q g := by
      rw [← hg]
      exact MulEquiv.ext fun _ => rfl
    rw [← this]
    exact Nat.card_congr (fixedEquiv β⁻¹ σ).toEquiv
  rw [hcongr]
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg1, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg1] at h
  have hsim := matrix_similarity Q g hg1
  have hbig := omega_centralizer_card_gt_big hK (Module.finrank_fin_fun K) hd Q hQ
    (matrixLinearEquiv g.val.left) c (multiplier Q g) hsq
    (CatalogueBOrthogonalLinearFixed.polar_similarity Q (matrixLinearEquiv g.val.left)
      (multiplier Q g) hsim)
    (matrixLinearEquiv_ne_smul_one g.val.left (hns hg1))
  have hineq := omega_linear_fixed_card_ge (by omega) Q hQ g hg1
  rw [hcard] at hineq
  have hXpos : 0 < Nat.card (matrixProjectiveDerived Q) := Nat.card_pos
  have h5 : Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap) ≤
      4 * Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hXpos
    calc Nat.card (matrixProjectiveDerived Q) *
          Nat.card (orthogonalOperatorCentralizer Q (matrixLinearEquiv g.val.left).toLinearMap)
        ≤ Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)) *
          (4 * Nat.card (matrixProjectiveDerived Q)) := hineq
      _ = Nat.card (matrixProjectiveDerived Q) *
          (4 * Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g))) := by ring
  exact (by omega : 2880 < Nat.card (fixedSubgroup (matrixProjectiveConjugation Q g)))

end Involution

theorem harrisOmegaLarge_of_concrete {t : StatedLieTag} {n f : ℕ}
    (H : ∀ (S : Type) [Group S] [Finite S], LieModel S t n 3 f →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (_ : S ≃* X),
        ∀ σ : MulAut X, orderOf σ = 2 → 2880 < Nat.card ↥(fixedSubgroup σ)) :
    HarrisOmegaLarge t n f := by
  intro S _ _ hm σ hσ
  obtain ⟨X, _, _, e, hX⟩ := H S hm
  have h := hX (MulAut.congr e σ) ((orderOf_congr e σ).trans hσ)
  rwa [← Nat.card_congr (fixedEquiv e σ).toEquiv] at h

theorem harrisOmegaLarge_POmegaOdd (hO : LieOrderFormulasInput) :
    HarrisOmegaLarge .POmegaOdd 3 1 := by
  refine harrisOmegaLarge_of_concrete fun S _ _ hm => ?_
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hC : StatedClassicalModel S .POmegaOdd 3 3 1 :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  let e' := coordinateOddWitnessEquiv K e
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK3)
  have hord := hO S .POmegaOdd 3 3 1 hadm hm
  have hmul : Nat.card S * 2 = lieOrderNumerator .POmegaOdd 3 3 := by
    simpa [lieOrderDivisor] using hord.2.1
  have hiso := HardMathSupport.Lang.UnitaryAutomorphisms.card_matrixIsometries_coordinateQuadOdd
    h2 3
  rw [hK3] at hiso
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd 3 K)) =
      4 * Nat.card (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := by
    rw [card_orthogonalGroup_eq_card_matrixIsometries, hiso, ← Nat.card_congr e'.toEquiv]
    omega
  refine ⟨matrixProjectiveDerived (coordinateQuadOdd 3 K), inferInstance, Finite.of_equiv S e', e',
    fun σ hσ => ?_⟩
  exact omega_fixed_card_gt_big hK3 (d := 2 * 3 + 1) (Or.inl rfl) _ hQ hrep hcard σ hσ

theorem harrisOmegaLarge_POmegaMinus (hO : LieOrderFormulasInput) :
    HarrisOmegaLarge .POmegaMinus 4 1 := by
  refine harrisOmegaLarge_of_concrete fun S _ _ hm => ?_
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hC : StatedClassicalModel S .POmegaMinus 4 3 1 :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  have hn : 1 ≤ 4 := by norm_num
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) hn K hK b c
    hirr e
  obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK b c hirr e
  let e' := coordinateMinusWitnessEquiv K hn b c e
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_three hK3)
  have hord := hO S .POmegaMinus 4 3 1 hadm hm
  have hmul : Nat.card S * 2 = lieOrderNumerator .POmegaMinus 4 3 := by
    simpa [lieOrderDivisor] using hord.2.1
  have hiso :=
    HardMathSupport.Lang.UnitaryAutomorphisms.card_matrixIsometries_coordinateQuadMinus
      h2 4 hn hirr
  rw [hK3] at hiso
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (coordinateQuadMinus 4 K hn b c)) =
      4 * Nat.card (matrixProjectiveDerived (coordinateQuadMinus 4 K hn b c)) := by
    rw [card_orthogonalGroup_eq_card_matrixIsometries, hiso, ← Nat.card_congr e'.toEquiv]
    omega
  refine ⟨matrixProjectiveDerived (coordinateQuadMinus 4 K hn b c), inferInstance,
    Finite.of_equiv S e', e', fun σ hσ => ?_⟩
  exact omega_fixed_card_gt_big hK3 (d := 2 * 4) (Or.inr rfl) _ hQ hrep hcard σ hσ

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
