module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaField
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClTwoPart

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Family


namespace FiveCl

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms in
theorem two_pow_dvd_of_orthogonalOperatorCentralizer_component {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5 ^ f) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (hV : 7 ≤ finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    {L : Subgroup (orthogonalOperatorCentralizer Q A.toLinearMap)} (hL : IsComponent L)
    (hLm : LieModel (L ⧸ center L) .PSL 2 2 2) :
    2 ^ finrank K V ∣ Nat.card (orthogonalOperatorCentralizer Q A.toLinearMap) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow f
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
      have hc := square_kernels_isCompl A d b hb h2 hsquare hroot
      rw [Nat.card_congr (positiveSquareKernelCentralizerEquiv Q A d μ b d.ne_zero hb h2 hsquare
        hroot hsim hpos).toEquiv, Nat.card_prod, ← Submodule.finrank_add_eq_of_isCompl hc,
        pow_add]
      exact Nat.mul_dvd_mul (ClTwoPart.two_pow_finrank_dvd_card_orthogonalGroup h2 _)
        (ClTwoPart.two_pow_finrank_dvd_card_orthogonalGroup h2 _)
    ·
      exfalso
      have hdimP := (negative_square_kernel_geometry Q hQ A d μ b d.ne_zero hb h2 hsquare hroot
        hsim hneg).2.2.2.2.1
      let e' := (negativeSquareKernelCentralizerEquiv Q hQ A d μ b d.ne_zero hb h2 hsquare hroot
        hsim hneg).trans (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K _))
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      obtain ⟨h22, -⟩ := eq_of_component_GL hf hK (by omega) hL' hL'm
      omega
  · exfalso
    have hs := CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare
    let := scalarField A.toLinearMap d hsq hs
    let := evaluationModule A.toLinearMap
    let := scalarAlgebra_finite_type A.toLinearMap d hsq hs
    let := evaluationModule_finite A.toLinearMap
    have hE : Nat.card (scalarAlgebra A.toLinearMap) = (5 ^ f) ^ 2 := by
      rw [scalarAlgebra_card A.toLinearMap d hsq hs, hK]
    have hdimE := evaluationModule_finrank
      A.toLinearMap d hsq hs
    rcases hsign with hpos | hneg
    ·
      have hadj := positive_square_adjoint Q A d μ d.ne_zero hsquare hsim hpos
      let e' := actualPositiveCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      have h1 := (oddFiveOrthComponentInput_holds _ _ (2 * f) (by omega)
        (by rw [hE, ← pow_mul, mul_comm]) _
        (actualPositiveQuadratic_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ h2)
        (by omega) _ hL' hL'm).1
      omega
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
      have hpow : ∀ z, (conjugation A.toLinearMap d hsq hs).toRingEquiv z = z ^ (5 ^ f) := by
        intro z
        rw [← hK]
        exact conjugation_eq_card_power A.toLinearMap d hsq hs h2 z
      let e' := actualNegativeCentralizerEquiv Q A.toLinearMap d d.ne_zero hsq hs hadj h2
      have hL' := LocalCores.isComponent_map_mulEquiv e' hL
      have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
        (L.equivMapOfInjective e'.toMonoidHom e'.injective) hLm
      obtain ⟨h22, -⟩ := eq_of_component_unitary hf hE (by omega) _
        (actualNegativeHermitian_isSymm Q A.toLinearMap d d.ne_zero hsq hs hadj)
        (actualNegativeHermitian_nondegenerate Q A.toLinearMap d d.ne_zero hsq hs hadj hQ)
        hsig hne hpow hL' hL'm
      omega

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
  CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer in
theorem false_of_linear_omega {K : Type} [Field K] [Finite K] {d f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 5 ^ f) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (hidx : (orthogonalDerived Q).index = 4)
    (hker : ∀ g' : similarityPairs Q, matrixProjectiveConjugationHom Q g' = 1 ↔
      g'.val.right = 1 ∧ ∃ a : Kˣ, g'.val.left = GeneralLinearGroup.scalar (Fin d) a)
    (g : similarityPairs Q) (hg : g.val.right = 1)
    (hord : orderOf (matrixProjectiveConjugationHom Q g) = 2)
    (h : FiveA5Group (fixedSubgroup (matrixProjectiveConjugationHom Q g))) : False := by
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; omega)
  have hodd : Odd (Nat.card K) := by rw [hK]; exact FiveList.odd_five_pow f
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨L, hL, hLm⟩ := h.1
  obtain ⟨-, c, hc⟩ := (hker (g * g)).mp (by
    rw [map_mul, ← pow_two, ← hord, pow_orderOf_eq_one])
  have hsq : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = (c : K) • x := by
    intro x
    have h := coordinateSemilinearMap_sq_apply g.val c (by rw [hg, one_pow]) hc x
    rwa [coordinateSemilinearMap_eq_matrix g.val hg] at h
  set A := matrixLinearEquiv g.val.left with hAdef
  have hsim := matrix_similarity Q g hg
  let Φ := linearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ (by omega)) g hg
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective Φ.toMonoidHom Φ.injective) hLm
  obtain ⟨M, hM, ⟨eLM⟩⟩ := CatLeafProof.exists_component_of_normalQuotientFixed
    (orthogonalDerived Q) (scalarSigns Q) (scalarSigns_central Q)
    (similarityConjugation Q A (multiplier Q g) hsim)
    (orthogonalDerived_invariant Q A (multiplier Q g) hsim)
    (scalarSigns_invariant Q A (multiplier Q g) hsim) hL'
  have hMm := LieType.CurtisTits.lieModel_of_mulEquiv eLM hL'm
  let eC := fixedCentralizerEquiv Q A (multiplier Q g) hsim
  have hN := LocalCores.isComponent_map_mulEquiv eC hM
  have hNm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (M.equivMapOfInjective eC.toMonoidHom eC.injective) hMm
  have h2d := two_pow_dvd_of_orthogonalOperatorCentralizer_component hf hK
    (by rw [Module.finrank_fin_fun]; omega) Q hQ A c (multiplier Q g) hsq
    (polar_similarity Q A (multiplier Q g) hsim) hN hNm
  rw [Module.finrank_fin_fun] at h2d
  have hfix :
      2 ^ d ∣ Nat.card (fixedSubgroup (similarityConjugation Q A (multiplier Q g) hsim)) := by
    rw [Nat.card_congr eC.toEquiv]
    exact h2d
  have h32 :
      2 ^ 5 ∣ Nat.card (fixedSubgroup (projectiveConjugation Q A (multiplier Q g) hsim)) := by
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨t, ht⟩ := he
      exact ClTwoPart.two_pow_dvd_card_fixed_orthogonal_quotient hidx _ _ _
        ((pow_dvd_pow 2 (by omega : 5 + 3 ≤ d)).trans hfix)
    · exact ClTwoPart.two_pow_dvd_card_fixed_orthogonal_quotient_of_odd h2
        (by rwa [Module.finrank_fin_fun]) hidx _ _ _
        ((pow_dvd_pow 2 (by omega : 5 + 2 ≤ d)).trans hfix)
  have hcard : Nat.card (fixedSubgroup (matrixProjectiveConjugationHom Q g)) =
      Nat.card (fixedSubgroup (projectiveConjugation Q A (multiplier Q g) hsim)) :=
    Nat.card_congr Φ.toEquiv
  exact h.not_dvd (by rw [hcard]; simpa using h32)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent CatalogueBOrthogonalFieldFixed
  CatalogueBOrthogonalLinearFixed CatalogueBOrthogonalFixedTransfer in
theorem false_of_field_omega {K : Type} [Field K] [Finite K] {d f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 5 ^ f) (hdim : d = 2 * n + 1 ∧ 3 ≤ n ∨ d = 2 * n ∧ 4 ≤ n)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1) (hσ : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {L : Subgroup (fixedSubgroup (matrixProjectiveConjugationHom Q g))} (hL : IsComponent L)
    (hLm : LieModel (L ⧸ center L) .PSL 2 2 2) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have : CharP K 5 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 5]; norm_num)
  have hd : 0 < d := by omega
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; exact hd)
  set σ := g.val.right with hσdef
  set τ₀ := coordinateSemilinearMap g.val with hτ₀
  set μ := multiplier Q g with hμ
  have hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x := coordinateSemilinearMap_smul g.val
  have hsim : ∀ x, Q (τ₀ x) = (μ : K) * σ (Q x) := multiplier_spec Q g
  have hsquare : ∀ x, τ₀ (τ₀ x) = (c : K) • x := coordinateSemilinearMap_sq_apply g.val c hσ2 hc
  let Φ := semilinearFixedEquiv Q (exists_ne_zero_of_polarBilin_nondegenerate Q hQ hd) g
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hform := semilinear_polar_similarity Q σ τ₀ μ hsim
  have hfixed := square_scalar_fixed σ τ₀ (c : K) hsemi hsquare
  have hmu := square_multiplier_identity σ hσ2 Q.polarBilin hQ τ₀ (μ : K) (c : K) hform hsquare
  obtain ⟨b, c', hb, hc'⟩ := exists_normalizing_units σ hσ2 hσ μ c hfixed hmu
  let T := normalizedOperator τ₀ b
  let hs := normalizedOperator_semilinear σ τ₀ b hsemi
  let hf' := normalized_form_identity σ Q.polarBilin τ₀ μ b c' hform hc'
  have hT := normalizedOperator_involutive σ τ₀ c b hsemi hsquare hb
  let : Module.Finite (fixedSubfield K σ) (fixedSubspace σ T hs) := by
    obtain ⟨e, d', hd'⟩ := exists_fixedSpace_basis σ hσ2 hσ h2 T hT hs
    exact Module.Finite.of_basis d'
  have hnd := descendedBilinear_nondegenerate σ T hs Q.polarBilin c' hf' hσ2 hσ h2 hT hsym hQ
  have hQ0 : (descendedQuadratic σ T hs Q.polarBilin c' hf').polarBilin.Nondegenerate := by
    rw [descendedQuadratic_polarBilin σ T hs Q.polarBilin c' hf' hsym h2]
    exact hnd
  let e : semilinearOrthogonalCentralizer Q τ₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup
        (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc') := by
    exact Eq.ndrec (motive := fun R : QuadraticForm K (Fin d → K) =>
      semilinearOrthogonalCentralizer R τ₀ ≃*
        TauCeti.QuadraticMap.orthogonalGroup
          (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc'))
      (originalDescentCentralizerEquiv σ τ₀ b hsemi Q.polarBilin μ c' hform hc'
        hσ2 hσ h2 hsym c hsquare hb) (originalQuadratic_polar_eq Q h2)
  let Θ := (semilinearFixedCentralizerEquiv Q σ τ₀ μ hsemi hsim).trans e
  have hcard := CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (fixedSubfield K σ) ∣ 5 ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : 5 ^ f = 5 ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hk : Nat.card (fixedSubfield K σ) = 5 ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by omega
  have hdimW : Module.finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = 2 * n + 1 ∧ 3 ≤ n ∨
      Module.finrank (fixedSubfield K σ) (fixedSubspace σ T hs) = 2 * n ∧ 4 ≤ n := by
    rw [fixedSubspace_finrank σ hσ2 hσ h2 T hT hs, Module.finrank_fin_fun]
    exact hdim
  obtain ⟨hΩq, τ', n', hne, hadm, hlie⟩ := FiveList.orthogonal_derived_lieModel_ne_PSL hp
    (by norm_num) hf2 hk (originalDescendedQuadratic σ τ₀ b hsemi Q.polarBilin μ c' hform hc') hQ0
    hdimW
  have hD : IsQuasisimple (commutator (fixedSubgroup
      (semilinearConjugation Q σ τ₀ μ hsemi hsim))) :=
    LocalCores.isQuasisimple_of_mulEquiv (CatLeafProof.commutatorEquiv Θ).symm hΩq
  have hDN : ∀ x ∈ commutator (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim)),
      (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ orthogonalDerived Q := by
    intro x hx
    have h1 : (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        (commutator (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim))).map
          (fixedSubgroup (semilinearConjugation Q σ τ₀ μ hsemi hsim)).subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [map_commutator_eq, Subgroup.range_subtype] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  obtain ⟨eZ⟩ := CatLeafProof.nonempty_centerQuotient_equiv_of_normalQuotientFixed
    (orthogonalDerived Q) (scalarSigns Q) (scalarSigns_central Q)
    (semilinearConjugation Q σ τ₀ μ hsemi hsim)
    (semilinear_orthogonalDerived_invariant Q σ τ₀ μ hsemi hsim)
    (semilinear_scalarSigns_invariant Q σ τ₀ μ hsemi hsim) hDN hD hL'
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eTot := ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eZ).trans
    (QuotientGroup.congr _ _ (CatLeafProof.commutatorEquiv Θ)
      (Subgroup.map_center_eq (CatLeafProof.commutatorEquiv Θ)))
  have hmod : LieModel (L ⧸ center L) τ' n' 5 (f / 2) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm hlie
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hLm (by norm_num) hadm hmod
  exact hne h1

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation in
theorem fiveA5_of_semilinearRepresentation {J : Type} [Group J] {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hrep : SemilinearRepresentation Q)
    (ψ : J ≃* matrixProjectiveDerived Q) (α : MulAut J) (hα : orderOf α = 2)
    (h : FiveA5Group (fixedSubgroup α)) :
    ∃ g : similarityPairs Q, g.val.right ^ 2 = 1 ∧
      orderOf (matrixProjectiveConjugationHom Q g) = 2 ∧
      FiveA5Group (fixedSubgroup (matrixProjectiveConjugationHom Q g)) := by
  set α' := MulAut.congr ψ α with hα'def
  have hα' : orderOf α' = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have h2 : α' * α' = 1 := by
    have h2 := pow_orderOf_eq_one α'
    rw [hα'] at h2
    rw [← pow_two]
    exact h2
  have h1 : α' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα'
    exact absurd hα' (by norm_num)
  obtain ⟨β, g, hg, hσ2, -, -, -⟩ := hrep.2 α' h2 h1
  have hc : MulAut.congr β⁻¹ α' = β⁻¹ * α' * β := MulEquiv.ext fun _ => rfl
  have hord : orderOf (matrixProjectiveConjugationHom Q g) = 2 := by
    rw [← hg, ← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α').trans hα'
  exact ⟨g, hσ2, hord, h.of_mulEquiv ((CatLeafProof.fixedSubgroupCongrEquiv ψ α).trans
    (((CatLeafProof.fixedSubgroupCongrEquiv β⁻¹ α').trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))).trans
        (MulEquiv.subgroupCongr (congrArg fixedSubgroup hg))))⟩

end FiveCl

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation in
theorem oddFiveSL2ListFamilyInput_POmegaOdd_holds : OddFiveSL2ListFamilyInput .POmegaOdd := by
  intro J _ _ hJ hna m f hadm hJm τ hτ
  exfalso
  have hf : 1 ≤ f := hadm.2.1
  have hm : 3 ≤ m := hadm.2.2.1
  have h5 := fiveA5Group_of_catSL2Hyp hτ
  have hC : StatedClassicalModel J .POmegaOdd m 5 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hJm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hJm) K hK e
  obtain ⟨g, hσ2, hord, hg5⟩ := FiveCl.fiveA5_of_semilinearRepresentation hrep
    (coordinateOddWitnessEquiv K e) τ hτ.1 h5
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd m K))) .POmegaOdd
      m 5 f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd hstated K hK (MulEquiv.refl _)
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT
    hAP
  by_cases hσ : g.val.right = 1
  · have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card
      (by rw [hK]; exact FiveList.odd_five_pow f)
    let P := fun i : Fin m =>
      ClTwoPart.hypPairMap (coordinateOddIsometry m K) (ClassicalGroups.Orthogonal.oddPair K i)
    have hP : ∀ {i j : Fin m}, i ≠ j → (P i).Orth (P j) := fun hij =>
      ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.oddPair_orth hij)
    have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
      (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    exact FiveCl.false_of_linear_omega hf hK (by omega) hnd hidx hker g hσ hord hg5
  · obtain ⟨c, hc⟩ := CatLeafProof.exists_twisted_square_scalar (fun g' h => (hker g').mp h) g
      hord
    obtain ⟨L, hL, hLm⟩ := hg5.1
    exact FiveCl.false_of_field_omega hf hK (Or.inl ⟨rfl, hm⟩) hnd g hσ2 hσ c hc hL hLm

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation in
theorem oddFiveSL2ListFamilyInput_POmegaPlus_holds : OddFiveSL2ListFamilyInput .POmegaPlus := by
  intro J _ _ hJ hna m f hadm hJm τ hτ
  exfalso
  have hf : 1 ≤ f := hadm.2.1
  have hm : 4 ≤ m := hadm.2.2
  have h5 := fiveA5Group_of_catSL2Hyp hτ
  have hC : StatedClassicalModel J .POmegaPlus m 5 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hJm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hJm) K hK e
  obtain ⟨g, hσ2, hord, hg5⟩ := FiveCl.fiveA5_of_semilinearRepresentation hrep
    (coordinatePlusWitnessEquiv K e) τ hτ.1 h5
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus m K))) .POmegaPlus
      m 5 f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT
    hAP
  by_cases hσ : g.val.right = 1
  · have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card
      (by rw [hK]; exact FiveList.odd_five_pow f)
    let P := fun i : Fin m =>
      ClTwoPart.hypPairMap (coordinatePlusIsometry m K) (ClassicalGroups.Orthogonal.plusPair K i)
    have hP : ∀ {i j : Fin m}, i ≠ j → (P i).Orth (P j) := fun hij =>
      ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.plusPair_orth hij)
    have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
      (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    exact FiveCl.false_of_linear_omega hf hK (by omega) hnd hidx hker g hσ hord hg5
  · obtain ⟨c, hc⟩ := CatLeafProof.exists_twisted_square_scalar (fun g' h => (hker g').mp h) g
      hord
    obtain ⟨L, hL, hLm⟩ := hg5.1
    exact FiveCl.false_of_field_omega hf hK (Or.inr ⟨rfl, hm⟩) hnd g hσ2 hσ c hc hL hLm

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation in
theorem oddFiveSL2ListFamilyInput_POmegaMinus_holds : OddFiveSL2ListFamilyInput .POmegaMinus := by
  intro J _ _ hJ hna m f hadm hJm τ hτ
  exfalso
  have hf : 1 ≤ f := hadm.2.1
  have hm : 4 ≤ m := hadm.2.2
  have hn : 1 ≤ m := by omega
  have h5 := fiveA5Group_of_catSL2Hyp hτ
  have hC : StatedClassicalModel J .POmegaMinus m 5 f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hJm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hJm) hn K hK b c
    hirr e
  obtain ⟨g, hσ2, hord, hg5⟩ := FiveCl.fiveA5_of_semilinearRepresentation hrep
    (coordinateMinusWitnessEquiv K hn b c e) τ hτ.1 h5
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus m K b c)))
      .POmegaMinus m 5 f := ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT
    hAP
  by_cases hσ : g.val.right = 1
  · have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card
      (by rw [hK]; exact FiveList.odd_five_pow f)
    let P := fun i : Fin (m - 1) =>
      ClTwoPart.hypPairMap (coordinateMinusIsometry m K hn b c)
        (ClassicalGroups.Orthogonal.minusPair (n := m) K b c i)
    have hP : ∀ {i j : Fin (m - 1)}, i ≠ j → (P i).Orth (P j) := fun hij =>
      ClTwoPart.hypPairMap_orth _ (ClassicalGroups.Orthogonal.minusPair_orth hij)
    have hidx := ClTwoPart.index_orthogonalDerived_eq_four h2 hnd
      (hP (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
      (hP (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    exact FiveCl.false_of_linear_omega hf hK (by omega) hnd hidx hker g hσ hord hg5
  · obtain ⟨c₀, hc₀⟩ := CatLeafProof.exists_twisted_square_scalar (fun g' h => (hker g').mp h) g
      hord
    obtain ⟨L, hL, hLm⟩ := hg5.1
    exact FiveCl.false_of_field_omega hf hK (Or.inr ⟨rfl, hm⟩) hnd g hσ2 hσ c₀ hc₀ hL hLm

end Family

end CFSG.SeitzReduction.RankOne
