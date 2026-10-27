module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Order8PSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallU3Bar
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner4Dvd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSpNineExcl
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphKill
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3Model

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatFC.PSLSmall
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def Order8Free {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → HasOrder8 σ

@[expose] def Order8Or2Pow6 {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D →
    HasOrder8 σ ∨ 2 ^ 6 ∣ Nat.card ↥(fixedSubgroup σ)

theorem Order8Or2Pow6.of_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (σ : MulAut S)
    (h : Order8Or2Pow6 (MulAut.congr e σ)) : Order8Or2Pow6 σ := by
  intro D hD
  have hcard : Nat.card (fixedSubgroup (MulAut.congr e σ)) = Nat.card (fixedSubgroup σ) :=
    (Nat.card_congr (fixedEquiv e σ).toEquiv).symm
  rcases h _ (a6Hyp_congr e σ D hD) with ⟨x, hx⟩ | h2
  · refine Or.inl ⟨(fixedEquiv e σ).symm x, ?_⟩
    rw [← hx]
    exact orderOf_injective (fixedEquiv e σ).symm.toMonoidHom (fixedEquiv e σ).symm.injective x
  · exact Or.inr (by rwa [hcard] at h2)

theorem Order8Free.of_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (σ : MulAut S)
    (h : Order8Free (MulAut.congr e σ)) : Order8Free σ := by
  intro D hD
  obtain ⟨x, hx⟩ := h _ (a6Hyp_congr e σ D hD)
  refine ⟨(fixedEquiv e σ).symm x, ?_⟩
  rw [← hx]
  exact orderOf_injective (fixedEquiv e σ).symm.toMonoidHom (fixedEquiv e σ).symm.injective x

section Two

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatLeafProof (psl_two_normal_form)

variable {K : Type} [Field K] [Finite K]

theorem order8Free_psl_two_core (hK : Nat.card K = 81)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 2) K)) (hσ : orderOf σ = 2) :
    Order8Free σ := by
  intro D hD
  have hsq0 : σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  obtain ⟨A, τ, hAτ⟩ := psl_two_normal_form σ
  by_cases hτ : τ = 1
  · have h1 : σ = innerDiagonalAction 2 K A := by
      rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
    subst h1
    exact (inner_two_false (by rw [hK]; norm_num)
      (two_ne_zero_of_odd_card' (by rw [hK]; decide)) hσ hD).elim
  · have hsq : CatalogueBLinearSemilinear.semilinearAction 2 K A τ ^ 2 = 1 := by
      rw [← hAτ]; exact hsq0
    have hK' : Nat.card K = 3 ^ 4 := by rw [hK]; norm_num
    obtain ⟨heven, hτc, H, hα⟩ :=
      CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy 2 K 3 4 Nat.prime_three
        (by decide) (by norm_num) hK' le_rfl (Or.inr (by rw [hK]; norm_num)) A τ hτ hsq
    have hτ2 : τ ^ 2 = 1 := frobenius_sq_eq_one hK' heven hτc
    have hc : MulAut.congr (innerDiagonalAction 2 K H) (pslFieldAut (Fin 2) K τ) =
        CatalogueBLinearSemilinear.semilinearAction 2 K A τ :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr (innerDiagonalAction 2 K H)
        (pslFieldAut (Fin 2) K τ) = _).trans hα.symm
    have h8 := (hasOrder8_pslFieldAut_two hK hτ2 hτ).congr (innerDiagonalAction 2 K H)
    rw [hc, ← hAτ] at h8
    exact h8

end Two

section Three

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearHigherB

theorem order8Free_psl_three_core (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 3) K))
    (hσ : orderOf σ = 2) : Order8Free σ := by
  intro D hD
  have hsq0 : σ ^ 2 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ] at this
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  rcases normal_form_ge_three (by norm_num : 3 ≤ 3) σ with
    ⟨A, τ, hAτ⟩ | ⟨A, hA⟩ | ⟨A, τ, hτ, hAτ⟩
  · by_cases hτ : τ = 1
    · have h1 : σ = innerDiagonalAction 3 K A := by
        rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
      subst h1
      exact (inner_three_false hK (two_ne_zero_of_odd_card' hodd) hσ hD).elim
    · have hsq : CatalogueBLinearSemilinear.semilinearAction 3 K A τ ^ 2 = 1 := by
        rw [← hAτ]; exact hsq0
      subst hAτ
      exact (noA6_semilinear_three hO hK A hτ hsq D hD).elim
  · subst hA
    have hsymm : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = (A : Matrix (Fin 3) (Fin 3) K) := by
      rcases CatalogueBGraphForm.pureGraph_involution_form_data 3 K (by norm_num) hodd' A hsq0 with
        h | ⟨-, h⟩
      · exact h
      · exact absurd h (by decide)
    obtain ⟨z, t, hz, ht, hzt⟩ :=
      PSLSmallGraph3.exists_dihedral hodd' hK A (transpose_inv_of_transpose_eq A hsymm)
    exact ⟨z, hz⟩
  · subst hAτ
    exact (graphField_three_false hO hK A hτ hσ hD).elim

end Three

section Four

open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.ComponentClassification.CatFC.PSLSmall.Graph4

variable {K : Type} [Field K] [Finite K]

theorem inner_four_two_pow_six_of_a6Hyp (hK : Nat.card K = 3) (htwo : (2 : K) ≠ 0)
    {A : GL (Fin 4) K} (hσ : orderOf (innerDiagonalAction 4 K A) = 2)
    {D : Subgroup ↥(fixedSubgroup (innerDiagonalAction 4 K A))}
    (h : A6Hyp (innerDiagonalAction 4 K A) D) :
    2 ^ 6 ∣ Nat.card (fixedSubgroup (innerDiagonalAction 4 K A)) := by
  obtain ⟨hne, hinv⟩ := inner_proj_data (by norm_num) (Or.inl (by norm_num)) hσ
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · exact (inner_four_split_false hK htwo hσ h hsq hsquare).elim
  · exact inner_four_quadratic_two_pow_six hK htwo hsquare hsq

theorem order8Or2Pow6_psl_four_core (hO : LieOrderFormulasInput) (hK : Nat.card K = 3)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin 4) K)) (hσ : orderOf σ = 2) :
    Order8Or2Pow6 σ := by
  intro D hD
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hodd'
  rcases normal_form_ge_three (by norm_num : 3 ≤ 4) σ with
    ⟨A, τ, hAτ⟩ | ⟨A, hA⟩ | ⟨A, τ, hτ, hAτ⟩
  · have hτ : τ = 1 := eq_one_of_card_three hK τ
    have h1 : σ = innerDiagonalAction 4 K A := by
      rw [hAτ, hτ, CatalogueBLinearSemilinear.semilinearAction_one_field]
    subst h1
    exact Or.inr (inner_four_two_pow_six_of_a6Hyp hK htwo hσ hD)
  · subst hA
    have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by
      have := pow_orderOf_eq_one (pureGraphAction 4 K A)
      rwa [hσ] at this
    have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd' A hsq2
    obtain ⟨hDc, hDZ⟩ := hD.component
    obtain ⟨N, hN, ⟨eDN⟩⟩ := pureGraph_component_transfer A hDc
    have hNA : Nonempty (N ⧸ center N ≃* alternatingGroup (Fin 6)) := ⟨eDN.symm.trans hDZ.some⟩
    have hdim : Module.finrank K (Fin 4 → K) = 4 := by rw [Module.finrank_fin_fun]
    refine Or.inl ?_
    rcases hform with hsymm | ⟨halt, -⟩
    · by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
          ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
      ·
        exfalso
        have hR := transpose_inv_of_transpose_eq A hsymm
        have hQ₀ : (matrixQuadraticForm A⁻¹).polarBilin.Nondegenerate :=
          polarBilin_matrixQuadraticForm_nondegenerate hodd' A⁻¹ hR
        let e₁ : ↥(CatalogueBGraphForm.isometryGroup 4 K A⁻¹) ≃*
            ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
          (isometryGroupEquiv A⁻¹).symm.trans
            (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd' A⁻¹ hR).symm)
        have hN₀ : IsComponent (N.map e₁.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e₁ hN
        haveI : Group.IsSolvable
            ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
          ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
            hodd (matrixQuadraticForm A⁻¹) hQ₀ hdim hS).2 hK).1
        exact CatLeafProof.not_isComponent_of_isSolvable hN₀
      · exact nonsplit_hasOrder8 hK A hsymm hS
    ·
      exfalso
      have hR := transpose_inv_of_transpose_eq_neg A halt
      let eI := isometryGroupEquiv A⁻¹
      have hN' : IsComponent (N.map eI.symm.toMonoidHom) :=
        LocalCores.isComponent_map_mulEquiv eI.symm hN
      have hNA' : Nonempty (↥(N.map eI.symm.toMonoidHom) ⧸ center ↥(N.map eI.symm.toMonoidHom) ≃*
          alternatingGroup (Fin 6)) :=
        ⟨(centerQuotient_map_equiv eI.symm N).some.symm.trans hNA.some⟩
      have hmodel := CatLeafProof.X10Sp.centralModel_isometryGroup_component (ℓ := 3) (j := 1)
        (m := 2) Nat.prime_three (by norm_num) (by norm_num) (by simpa using hK)
        (matrixForm A⁻¹) (matrixForm_isAlt hodd' A⁻¹ hR) (matrixForm_nondegenerate A⁻¹)
        (by rw [Module.finrank_fin_fun]) le_rfl hN'
      have h := a6sq_lieModel_a6 hO hNA' hmodel.1 (by norm_num) hmodel.2
      exact absurd h.1 (by decide)
  · exact absurd (eq_one_of_card_three hK τ) hτ

end Four

theorem order8Free_psl_two {S : Type} [Group S] (hadm : StatedLieAdmissible .PSL 2 3 4)
    (hm : LieModel S .PSL 2 3 4) {σ : MulAut S} (hσ : orderOf σ = 2) : Order8Free σ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  exact Order8Free.of_congr e σ
    (order8Free_psl_two_core (by rw [hK]; norm_num) _ ((orderOf_congr e σ).trans hσ))

theorem order8Free_psl_three (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (hadm : StatedLieAdmissible .PSL 3 3 2) (hm : LieModel S .PSL 3 3 2) {σ : MulAut S}
    (hσ : orderOf σ = 2) : Order8Free σ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  exact Order8Free.of_congr e σ
    (order8Free_psl_three_core hO (by rw [hK]; norm_num) _ ((orderOf_congr e σ).trans hσ))

theorem order8Or2Pow6_psl_four (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (hadm : StatedLieAdmissible .PSL 4 3 1) (hm : LieModel S .PSL 4 3 1) {σ : MulAut S}
    (hσ : orderOf σ = 2) : Order8Or2Pow6 σ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  exact Order8Or2Pow6.of_congr e σ
    (order8Or2Pow6_psl_four_core hO (by rw [hK]; norm_num) _ ((orderOf_congr e σ).trans hσ))

theorem order8Or2Pow6_psp_nine {S : Type} [Group S] (hadm : StatedLieAdmissible .PSp 2 3 2)
    (hm : LieModel S .PSp 2 3 2) {σ : MulAut S} (hσ : orderOf σ = 2) : Order8Or2Pow6 σ := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hm
  refine Order8Or2Pow6.of_congr e σ fun D hD => ?_
  exact PSpSmall.psp_nine_exclusion hK ((orderOf_congr e σ).trans hσ) hD

section UnitaryThree

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_primeFormP_of_lieModel')

theorem order8Free_psu_three_core (hO : LieOrderFormulasInput) {K : Type} [Field K]
    (h : UnitaryFieldData 3 2 K) (σ : MulAut (primeFormP h (idGram K 3))) (hσ : orderOf σ = 2) :
    Order8Free σ := by
  intro D hD
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 3 ^ 2 = 2) := by norm_num
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq σ
  have hff : primeFormFieldFactor h hC hn hq σ = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one σ
    rw [hσ] at h1
    rw [h1, map_one]
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · exfalso
    have hAσ : σ = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    subst hAσ
    exact psu_inner_three_two_false hO h A hσ hD
  · subst hAφ
    obtain ⟨Ψ⟩ := psu_graph_three_two_equiv h A φ hφ hσ
    obtain ⟨a₁, a₂, -, -, ha8, ha4⟩ := psu_graph_three_two_pair h A φ hφ Ψ
    exact ⟨a₁ * a₂, orderOf_eq_prime_pow (p := 2) (n := 2) ha4 ha8⟩

theorem order8Free_psu_three (hO : LieOrderFormulasInput) {S : Type} [Group S]
    (hadm : StatedLieAdmissible .PSU 3 3 2) (hm : LieModel S .PSU 3 3 2) {σ : MulAut S}
    (hσ : orderOf σ = 2) : Order8Free σ := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  exact Order8Free.of_congr ψ σ
    (order8Free_psu_three_core hO h _ ((orderOf_congr ψ σ).trans hσ))

end UnitaryThree

end CFSG.EvenSporadicStandard.M24Std.KForm
