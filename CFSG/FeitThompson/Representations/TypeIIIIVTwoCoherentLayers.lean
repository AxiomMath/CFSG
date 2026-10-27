module

public import CFSG.FeitThompson.Local.TypeIIIIVChiefData
public import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence
public import CFSG.FeitThompson.Representations.TypeIIIIVProperCoherentIndexBound
public import CFSG.FeitThompson.Representations.TypeThreeFourSecondDerivedFitting
public import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
public import CFSG.FeitThompson.Representations.TypePOrientedCoreFamily
import CFSG.FeitThompson.Representations.TypeIIIVCoherentCrossedRowData
import CFSG.FeitThompson.OddOrder.NormPointCharacterIdentity
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup NormalInducedFamily CFSG.FeitThompson.Prep05

universe u

theorem indClassFun_inst {L : Type*} [Group L] (i j : Fintype L) (K : Subgroup L) (θ : ↥K → ℂ) :
    @indClassFun L _ K i θ = @indClassFun L _ K j θ := by
  have h : i = j := Subsingleton.elim i j
  subst h; rfl

theorem prep06_hallCoreIn_eq_hallCoreOf' {G : Type*} [Group G] (M : Subgroup G) :
    CFSG.FeitThompson.Prep06.hallCoreIn M = hallCoreOf M := by
  rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, hallCoreOf_eq]

theorem prep06_fittingIn_eq_fittingOf' {G : Type*} [Group G] [Finite G] (M : Subgroup G) :
    CFSG.FeitThompson.Prep06.fittingIn M = fittingOf M := by
  rw [CFSG.FeitThompson.Prep06.fittingIn_eq, fittingOf_eq]

variable {G : Type u} [Group G]

theorem no_strict_between_of_isChiefLayer' {M H₀ : Subgroup G}
    (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    ∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) → ¬ (H₀ < H₁ ∧ H₁ < hallCoreOf M) := by
  intro H₁ hH₁ ⟨hlt₁, hlt₂⟩
  rcases hlayer.2.2 H₁ hH₁ hlt₁.le hlt₂.le with h | h
  · exact hlt₁.ne' h
  · exact hlt₂.ne h

theorem sup_hallCoreIn_centralizer_eq_commutator_commutator [Finite G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
        (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
      = ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
  have _ : Fintype G := Fintype.ofFinite G
  obtain ⟨hK', hHC, -, -⟩ := h₂ G hG M U W₁ W₂ hM htype hc
  rw [hHC, hK']

theorem centralizer_eq_commutator_self [Finite G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G) = ⁅U, U⁆ := by
  have _ : Fintype G := Fintype.ofFinite G
  exact (h₁ G hG M U W₁ W₂ hM htype hc).2.2.2.2.2.1

theorem le_normalizer_centralizer [Finite G]
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    M ≤ normalizer ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)
      : Subgroup G) : Set G) := by
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hnorm, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₅ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  rw [prep06_hallCoreIn_eq_hallCoreOf', ← centralizerIn_eq]
  exact hnorm

theorem commutator_derivedOf_eq_sup [Finite G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
        (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
        : Subgroup G).subgroupOf M)
      = ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ := by
  rw [sup_hallCoreIn_centralizer_eq_commutator_commutator h₂ hG hM htype hc,
    subgroupOf_commutator_commutator]

theorem commutator_derivedOf_eq_fittingRaw [Finite G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ = fittingRaw ↥M := by
  have _ : Fintype G := Fintype.ofFinite G
  obtain ⟨hK', -, -, -⟩ := h₂ G hG M U W₁ W₂ hM htype hc
  rw [← subgroupOf_commutator_commutator M, hK', prep06_fittingIn_eq_fittingOf',
    subgroupOf_fittingOf]

open scoped Classical in
theorem indFamKer_sup_eq_kerLayerIndFam_commutator [Fintype G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
          (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
          : Subgroup G).subgroupOf M)
      = kerLayerIndFam ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆
          (CFSG.FeitThompson.Prep06.derivedOf M) := by
  rw [indFamKer_eq_kerLayerIndFam, commutator_derivedOf_eq_sup h₂ hG hM htype hc]

open scoped Classical in
theorem hasCoherentMap_layer_one [Fintype G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
          (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
          : Subgroup G).subgroupOf M)) := by
  rw [commutator_derivedOf_eq_sup h₂ hG hM htype hc]
  exact hasCoherentMap_indFamKer_commutator h₃ h₄ hG hM htype hc

open scoped Classical in
theorem layer_one_subset_Irr [Fintype G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
      ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
        (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
        : Subgroup G).subgroupOf M) ⊆ Irr ↥M ∧
      ∀ f ∈ CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
          (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
          : Subgroup G).subgroupOf M), f 1 = (Nat.card W₁ : ℂ) := by
  classical
  have hfin : Finite G := Finite.of_fintype G
  have hsolvM : Group.IsSolvable ↥M := hG.solvable M hM.1
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hKs : Group.IsSolvable ↥(CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hprime : IsPrimeCyclicTIHyp (CFSG.FeitThompson.Prep06.derivedOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hfree := hc.fixesOnlyCommutatorCoset_subgroupOf (W₁ := W₁) hG.odd
  rw [indFamKer_sup_eq_kerLayerIndFam_commutator h₂ hG hM htype hc]
  refine ⟨FrobeniusQuotientLayer.kerLayerIndFam_commutator_subset_Irr hprime.mul_eq_univ hfree,
    fun f hf => ?_⟩
  rw [FrobeniusQuotientLayer.apply_one_of_mem_kerLayerIndFam_commutator hf, index_derivedOf hc]

open scoped Classical in
theorem exists_card_layer_one [Fintype G]
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ∃ n : ℕ,
      Nat.card (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
          (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
          : Subgroup G).subgroupOf M)) = n ∧ Even n ∧ 2 ≤ n ∧
        n * Nat.card W₁ =
          Subgroup.relIndex
            (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)) U - 1 := by
  classical
  have hfin : Finite G := Finite.of_fintype G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  have hsolvM : Group.IsSolvable ↥M := hG.solvable M hM.1
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  obtain ⟨-, hq, -, hqodd, -, -, hsemi₁, hsemi₂, -, -, -, hCU, hdir, -, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₅ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  have hprime : IsPrimeCyclicTIHyp (CFSG.FeitThompson.Prep06.derivedOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hfree := hc.fixesOnlyCommutatorCoset_subgroupOf (W₁ := W₁) hG.odd
  have hu : Subgroup.relIndex ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆
      (CFSG.FeitThompson.Prep06.derivedOf M)
      = Subgroup.relIndex
        (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)) U := by
    rw [commutator_derivedOf_eq_fittingRaw h₂ hG hM htype hc,
      relIndex_fittingRaw_derivedOf hc hsemi₁ hsemi₂ hdir, centralizerIn_eq,
      prep06_hallCoreIn_eq_hallCoreOf']
  rw [indFamKer_sup_eq_kerLayerIndFam_commutator h₂ hG hM htype hc]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (kerLayerIndFinset ⁅CFSG.FeitThompson.Prep06.derivedOf M,
      CFSG.FeitThompson.Prep06.derivedOf M⁆ (CFSG.FeitThompson.Prep06.derivedOf M)).card = n := ⟨_, rfl⟩
  have hcount := FrobeniusQuotientLayer.card_kerLayerIndFinset_commutator_mul_index
    (E := W₁.subgroupOf M) hprime.mul_eq_univ hfree
  rw [index_derivedOf hc, hu, hn] at hcount
  have hcard : Nat.card (kerLayerIndFam ⁅CFSG.FeitThompson.Prep06.derivedOf M,
      CFSG.FeitThompson.Prep06.derivedOf M⁆ (CFSG.FeitThompson.Prep06.derivedOf M)) = n := by
    rw [Nat.card_coe_set_eq, ← CentralSectionCoherence.coe_kerLayerIndFinset,
      Set.ncard_coe_finset, hn]
  have huodd : Odd (Subgroup.relIndex
      (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)) U) := by
    rw [← Subgroup.relIndex_subgroupOf hc.le_M_E]
    exact odd_relIndex_of_odd hG.odd M _ _
  have hu1 : 1 < Subgroup.relIndex
      (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)) U := by
    rw [prep06_hallCoreIn_eq_hallCoreOf', ← centralizerIn_eq]
    exact one_lt_relIndex_of_lt hCU
  obtain ⟨k, hk⟩ := huodd
  have hdvd2 : 2 ∣ n * Nat.card ↥W₁ := by omega
  have h2n : 2 ∣ n := (Nat.coprime_two_left.mpr hqodd).dvd_of_dvd_mul_right hdvd2
  have hq1 : 1 < Nat.card ↥W₁ := hq.one_lt
  refine ⟨n, hcard, (even_iff_two_dvd).mpr h2n, ?_, by omega⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exfalso; rw [h0] at hcount; omega
  · omega

open scoped Classical in
theorem star_mem_indFamKer [Fintype G] {M : Subgroup G} {K A : Subgroup ↥M}
    {f : ↥M → ℂ} (hf : f ∈ CFSG.FeitThompson.Prep06.indFamKer M K A) :
    star f ∈ CFSG.FeitThompson.Prep06.indFamKer M K A := by
  classical
  have hMfin : Fintype ↥M := Fintype.ofFinite _
  rw [CFSG.FeitThompson.Prep06.indFamKer_eq, mem_indFam] at hf ⊢
  obtain ⟨θ, ⟨hθ, hker⟩, rfl⟩ := hf
  obtain ⟨hirr, hne⟩ := mem_nonprincipalIrr.1 hθ
  have hKfin : Finite ↥K := Subtype.finite
  refine ⟨star θ, ⟨mem_nonprincipalIrr.2 ⟨star_mem_Irr hirr, ?_⟩, ?_⟩, ?_⟩
  · intro hcon
    refine hne ?_
    have := congrArg (fun g : ↥K → ℂ => star g) hcon
    simpa using this
  · intro x hx
    have h := hker x hx
    simp only [Pi.star_apply, RCLike.star_def]
    rw [h]
  · exact (indClassFun_inst _ hMfin K (star θ)).trans
      ((DisjointCoherentFamilies.indClassFun_star K θ).trans
        (congrArg star (indClassFun_inst hMfin _ K θ)))

open scoped Classical in
theorem star_mem_indFamDetectKer [Fintype G] {M : Subgroup G} {K C H : Subgroup ↥M}
    {f : ↥M → ℂ} (hf : f ∈ CFSG.FeitThompson.Prep06.indFamDetectKer M K C H) :
    star f ∈ CFSG.FeitThompson.Prep06.indFamDetectKer M K C H := by
  classical
  have hMfin : Fintype ↥M := Fintype.ofFinite _
  rw [CFSG.FeitThompson.Prep06.indFamDetectKer_eq, mem_indFam] at hf ⊢
  obtain ⟨θ, ⟨hθ, hker, x, hxH, hxne⟩, rfl⟩ := hf
  have hKfin : Finite ↥K := Subtype.finite
  refine ⟨star θ, ⟨?_, ?_, x, hxH, ?_⟩, ?_⟩
  · rw [← Irr_eq_irrChar] at hθ ⊢
    exact star_mem_Irr hθ
  · intro y hy
    have h := hker y hy
    simp only [Pi.star_apply, RCLike.star_def]
    rw [h]
  · simp only [Pi.star_apply, RCLike.star_def]
    exact fun hcon => hxne (by
      have := congrArg (starRingEnd ℂ) hcon
      simpa using this)
  · exact (indClassFun_inst _ hMfin K (star θ)).trans
      ((DisjointCoherentFamilies.indClassFun_star K θ).trans
        (congrArg star (indClassFun_inst hMfin _ K θ)))

theorem exists_isCoherentAt_of_hasCoherentMap [Finite G] [Fintype G]
    {M W₁ W₂ : Subgroup G} {S S₀ : Set (↥M → ℂ)} (hS : S = S₀)
    (h : CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂ S) :
    ∃ ν : Submodule.span ℤ S₀ →+ (G → ℂ), IsCoherentAt M S₀ (tauDerived M W₁ W₂) ν := by
  classical
  have _ : Fintype ↥M := Fintype.ofFinite _
  subst hS
  obtain ⟨ν, hiso, heq⟩ := h
  refine ⟨AddMonoidHom.mk' (fun f => ((ν f : virtualChars G) : G → ℂ))
    (fun a b => by simp), ?_, ?_, ?_⟩
  · intro f; exact (ν f).2
  · intro f g
    rw [cfIP_eq_cfInner_of_finite, cfIP_eq_cfInner_of_finite]
    exact (hiso f g).trans (cfInner_inst _ _ _ _)
  · intro f hf1
    change ((ν f : virtualChars G) : G → ℂ) = _
    rw [heq f hf1, tauDerived_eq_dadeTau]

open scoped Classical in
theorem not_hasCoherentMap_indFamKer_centralizer [Fintype G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ¬ CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        (Subgroup.subgroupOf
          (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)) M)) := by
  intro hcoh
  have hfin : Finite G := Finite.of_fintype G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨H₀, hH₀, hlayer⟩, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₅ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨-, -, -, -, hchief, -, -⟩ := h₁ G hG M U W₁ W₂ hM htype hc
  have hbot : H₀ = ⊥ := by
    refine hchief H₀ ?_ hlayer.1 ?_ ?_ ?_
    · rw [prep06_hallCoreIn_eq_hallCoreOf']; exact hlayer.2.1.le
    · rw [prep06_hallCoreIn_eq_hallCoreOf', ← centralizerIn_eq]; exact hH₀
    · rw [prep06_hallCoreIn_eq_hallCoreOf']; exact hlayer.2.1
    · intro H₁ hH₁
      rw [prep06_hallCoreIn_eq_hallCoreOf']
      exact no_strict_between_of_isChiefLayer' hlayer H₁ hH₁
  have hCeq : H₀ ⊔ centralizerIn U (hallCoreOf M)
      = U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G) := by
    rw [hbot, bot_sup_eq, centralizerIn_eq, prep06_hallCoreIn_eq_hallCoreOf']
  have hSeq : kerLayerIndFam ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M)
        (CFSG.FeitThompson.Prep06.derivedOf M)
      = derivedIndFamKer M (H₀ ⊔ centralizerIn U (hallCoreOf M)) := by
    rw [derivedIndFamKer_eq_kerLayerIndFam M (H₀ ⊔ centralizerIn U (hallCoreOf M)),
      subgroupOf_commutator_self]
    exact kerLayerIndFam_inst _ _ _ _
  have hS2 : CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
      = kerLayerIndFam ((H₀ ⊔ centralizerIn U (hallCoreOf M)).subgroupOf M)
        (CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [indFamKer_eq_kerLayerIndFam, hCeq]
  obtain ⟨ν, hν⟩ := exists_isCoherentAt_of_hasCoherentMap (hS2.trans hSeq) hcoh
  exact CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_layer_noncoherence h₃ h₄ h₅ G hG5 M U W₁ W₂
    hM htype hc H₀ hH₀ hlayer ⟨ν, hν⟩

theorem exists_subgroup_coe_eq_charValueKernel {K : Type*} [Group K] [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ irrChar ℂ K) : ∃ N : Subgroup K, (N : Set K) = charValueKernel θ := by
  obtain ⟨V, -, hV⟩ := mem_irrChar.1 hθ
  subst hV
  exact ⟨(Representation.asGroupHom V.ρ).ker, (charValueKernel_character V.ρ).symm⟩

open scoped Classical in
theorem disjoint_indFamKer_sup_indFamDetectKer [Fintype G] {M H C : Subgroup G}
    {K : Subgroup ↥M} [K.Normal] (hHn : (H.subgroupOf M).Normal) :
    Disjoint (CFSG.FeitThompson.Prep06.indFamKer M K ((H ⊔ C).subgroupOf M))
      (CFSG.FeitThompson.Prep06.indFamDetectKer M K (C.subgroupOf M) (H.subgroupOf M)) := by
  rw [Set.disjoint_left]
  intro f hf1 hf2
  rw [CFSG.FeitThompson.Prep06.indFamKer_eq, mem_indFam] at hf1
  rw [CFSG.FeitThompson.Prep06.indFamDetectKer_eq, mem_indFam] at hf2
  obtain ⟨θ₁, ⟨hθ₁, hk₁⟩, rfl⟩ := hf1
  obtain ⟨θ₂, ⟨hθ₂, -, x, hxH, hx⟩, he⟩ := hf2
  have hirr₁ : θ₁ ∈ Irr ↥K := (mem_nonprincipalIrr.1 hθ₁).1
  have hirr₂ : θ₂ ∈ Irr ↥K := by rw [Irr_eq_irrChar]; exact hθ₂
  obtain ⟨t, ht⟩ := (indClassFun_eq_iff_exists_conjClassFun K hirr₂ hirr₁).1 he
  apply hx
  rw [← ht, NormalInduction.conjClassFun_apply, NormalInduction.conjClassFun_apply, map_one]
  refine hk₁ _ ?_
  have h := hHn.conj_mem _ hxH t⁻¹
  rw [MulAut.conjNormal_apply]
  rw [mem_subgroupOf] at h ⊢
  exact le_sup_left (a := H) h

open scoped Classical in
theorem union_indFamKer_sup_indFamDetectKer [Fintype G] {M H C : Subgroup G}
    {K : Subgroup ↥M} (hHM : H ≤ M) (hCM : C ≤ M) (hHK : H.subgroupOf M ≤ K)
    (hCK : C.subgroupOf M ≤ K) :
    CFSG.FeitThompson.Prep06.indFamKer M K ((H ⊔ C).subgroupOf M) ∪
        CFSG.FeitThompson.Prep06.indFamDetectKer M K (C.subgroupOf M) (H.subgroupOf M)
      = CFSG.FeitThompson.Prep06.indFamKer M K (C.subgroupOf M) := by
  ext f
  simp only [Set.mem_union, CFSG.FeitThompson.Prep06.indFamKer_eq,
    CFSG.FeitThompson.Prep06.indFamDetectKer_eq, mem_indFam]
  constructor
  · rintro (⟨θ, ⟨hθ, hk⟩, rfl⟩ | ⟨θ, ⟨hθ, hk, x, hxH, hx⟩, rfl⟩)
    · exact ⟨θ, ⟨hθ, fun y hy => hk y (mem_subgroupOf.2
        (le_sup_right (a := H) (mem_subgroupOf.1 hy)))⟩, rfl⟩
    · refine ⟨θ, ⟨mem_nonprincipalIrr.2 ⟨by rw [Irr_eq_irrChar]; exact hθ, fun h1 => ?_⟩, hk⟩,
        rfl⟩
      subst h1
      exact hx rfl
  · rintro ⟨θ, ⟨hθ, hk⟩, rfl⟩
    by_cases hH : ∀ x : ↥K, (x : ↥M) ∈ H.subgroupOf M → θ x = θ 1
    · refine Or.inl ⟨θ, ⟨hθ, fun x hx => ?_⟩, rfl⟩
      have hθc : θ ∈ irrChar ℂ ↥K := by
        rw [← Irr_eq_irrChar]; exact (mem_nonprincipalIrr.1 hθ).1
      obtain ⟨N, hN⟩ := exists_subgroup_coe_eq_charValueKernel hθc
      have hle : H.subgroupOf M ⊔ C.subgroupOf M ≤ N.map K.subtype := by
        refine sup_le (fun y hy => ⟨⟨y, hHK hy⟩, ?_, rfl⟩) (fun y hy => ⟨⟨y, hCK hy⟩, ?_, rfl⟩)
        · rw [hN, mem_charValueKernel]; exact hH _ hy
        · rw [hN, mem_charValueKernel]; exact hk _ hy
      rw [subgroupOf_sup hHM hCM] at hx
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = x := Subtype.ext hyx
      subst this
      have hy' : y ∈ (N : Set ↥K) := hy
      rw [hN] at hy'
      exact mem_charValueKernel.1 hy'
    · push Not at hH
      obtain ⟨x, hx1, hx2⟩ := hH
      exact Or.inr ⟨θ, ⟨by rw [← Irr_eq_irrChar]; exact (mem_nonprincipalIrr.1 hθ).1, hk, x, hx1,
        hx2⟩, rfl⟩

theorem isChiefFactor_hallCore_bot_of_isChiefLayer {M : Subgroup G}
    (hlayer : IsChiefLayer M ⊥ (hallCoreOf M)) :
    IsChiefFactor (hallCore ↥M) (⊥ : Subgroup ↥M) := by
  have hHne : hallCore ↥M ≠ ⊥ := by
    intro h
    have h2 := hlayer.2.1
    rw [hallCoreOf_eq, h, Subgroup.map_bot] at h2
    exact lt_irrefl _ h2
  refine { normal_num := hallCore_normal, normal_den := inferInstance,
           lt := bot_lt_iff_ne_bot.2 hHne, not_lt_lt := ?_ }
  intro Z hZ hZbot hZlt
  have hN : Z.map M.subtype ≤ hallCoreOf M := by
    rw [hallCoreOf_eq]; exact Subgroup.map_mono hZlt.le
  rcases hlayer.2.2 _ (le_normalizer_map_subtype_of_normal hZ) bot_le hN with h | h
  · refine hZbot.ne' ?_
    rw [← Subgroup.map_bot M.subtype] at h
    exact Subgroup.map_injective M.subtype_injective h
  · refine hZlt.ne ?_
    rw [hallCoreOf_eq] at h
    exact Subgroup.map_injective M.subtype_injective h

theorem inf_hallCore_centralizer_le_bot_of_eq_bot {M U : Subgroup G} (hUM : U ≤ M)
    (h : CFSG.FeitThompson.Prep06.hallCoreIn M ⊓ centralizer (U : Set G) = ⊥) :
    hallCore ↥M ⊓ Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤ ⊥ := by
  intro x ⟨hxH, hxc⟩
  have hxG : (x : G) ∈ CFSG.FeitThompson.Prep06.hallCoreIn M ⊓ centralizer (U : Set G) := by
    refine ⟨⟨x, hxH, rfl⟩, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc ⟨g, hUM hg⟩
      (mem_subgroupOf.2 (by simpa using hg)))
  rw [h] at hxG
  exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hxG))

theorem isChiefLayer_bot_hallCoreOf [Finite G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsChiefLayer M ⊥ (hallCoreOf M) := by
  have _ : Fintype G := Fintype.ofFinite G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨H₀, hH₀, hlayer⟩, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₅ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨-, -, -, -, hchief, -, -⟩ := h₁ G hG M U W₁ W₂ hM htype hc
  have hbot : H₀ = ⊥ := by
    refine hchief H₀ ?_ hlayer.1 ?_ ?_ ?_
    · rw [prep06_hallCoreIn_eq_hallCoreOf']; exact hlayer.2.1.le
    · rw [prep06_hallCoreIn_eq_hallCoreOf', ← centralizerIn_eq]; exact hH₀
    · rw [prep06_hallCoreIn_eq_hallCoreOf']; exact hlayer.2.1
    · intro H₁ hH₁
      rw [prep06_hallCoreIn_eq_hallCoreOf']
      exact no_strict_between_of_isChiefLayer' hlayer H₁ hH₁
  rw [← hbot]; exact hlayer

theorem isPtypeCoreConfig_bot_of_typeIII_IV [Finite G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    PtypeCoreCoherence.IsPtypeCoreConfig M U W₁ W₂ (⊥ : Subgroup ↥M)
      (((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
      (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M) := by
  have _ : Fintype G := Fintype.ofFinite G
  exact
  { simple := hG.simple
    not_isMulCommutative := hG.nonabelian
    odd_card := hG.odd
    solvable_proper := hG.solvable
    isCoatom := hM
    isType := Or.inr htype
    isWitnessedPConfiguration := hc
    isChiefFactor := isChiefFactor_hallCore_bot_of_isChiefLayer
      (isChiefLayer_bot_hallCoreOf h₁ h₅ hG hM htype hc)
    centralizer_le_H0 := inf_hallCore_centralizer_le_bot_of_eq_bot hc.le_M_E
      (h₁ G hG M U W₁ W₂ hM htype hc).2.2.2.1
    A_subset := le_rfl
    A_conj := OrientedCoreFamily.commutator_sdiff_one_conj M
    centralizer_subset_A := fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩
    A0_eq :=
      (OrientedCoreFamily.image_bridgeSupport_commutator_eq_dadeA0 hc.le_M_W₁ hc.le_M_W₂).symm
    isDadeData := (h₃ G hG M U W₁ W₂ hM (htype.elim Or.inl (fun h => Or.inr (Or.inl h)))
      hc).2.2.2.1 }

theorem star_mem_coreDetectFam {M U : Subgroup G} [Fintype ↥M] {H0 : Subgroup ↥M} [H0.Normal]
    {f : ↥M → ℂ} (hf : f ∈ PtypeCoreCoherence.coreDetectFam M U H0) :
    star f ∈ PtypeCoreCoherence.coreDetectFam M U H0 := by
  rw [PtypeCoreCoherence.coreDetectFam_eq_indFam, mem_indFam] at hf ⊢
  obtain ⟨θ, hθ, rfl⟩ := hf
  refine ⟨star θ, ?_, DisjointCoherentFamilies.indClassFun_star _ θ⟩
  rw [mem_irrKer] at hθ ⊢
  obtain ⟨hirr, hk, hd⟩ := hθ
  refine ⟨?_, ?_, ?_⟩
  · rw [← Irr_eq_irrChar] at hirr ⊢; exact star_mem_Irr hirr
  · rw [charValueKernel_star]; exact hk
  · rw [charValueKernel_star]; exact hd

open scoped Classical in
theorem indFamDetectKer_subset_coreDetectFam [Fintype G] {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M)
      ⊆ PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M) := by
  rw [CFSG.FeitThompson.Prep06.derivedOf_eq]
  intro f hf
  rw [CFSG.FeitThompson.Prep06.indFamDetectKer_eq, mem_indFam] at hf
  obtain ⟨θ, ⟨hθ, hk, x, hxH, hx⟩, rfl⟩ := hf
  rw [PtypeCoreCoherence.coreDetectFam_eq_indFam]
  have hUK : U.subgroupOf M ≤ commutator ↥M := by
    rw [← OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc]; exact le_sup_right
  obtain ⟨N, hN⟩ := exists_subgroup_coe_eq_charValueKernel hθ
  set Cm := chiefActionKer (hallCore ↥M) (⊥ : Subgroup ↥M) (U.subgroupOf M) with hCm
  have hCmN : Cm ≤ N.map (commutator ↥M).subtype := by
    intro y hy
    have hyU : y ∈ U.subgroupOf M := chiefActionKer_le _ _ _ hy
    rw [hCm, OrientedCoreFamily.chiefActionKer_bot] at hy
    refine ⟨⟨y, hUK hyU⟩, ?_, rfl⟩
    rw [hN, mem_charValueKernel]
    refine hk _ ?_
    rw [mem_subgroupOf]
    refine ⟨mem_subgroupOf.1 hyU, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨g', hg', rfl⟩ := hg
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy.2 g' hg')
  rw [mem_indFam]
  refine ⟨θ, ?_, rfl⟩
  rw [mem_irrKer_iff_values]
  refine ⟨hθ, fun y hy => ?_, ⟨x, ?_, hx⟩⟩
  · rw [mem_subgroupOf, bot_sup_eq] at hy
    obtain ⟨z, hz, hzy⟩ := hCmN (Subgroup.commutator_le_self Cm hy)
    have : z = y := Subtype.ext hzy
    subst this
    have hz' : z ∈ (N : Set _) := hz
    rw [hN] at hz'
    exact mem_charValueKernel.1 hz'
  · rw [mem_subgroupOf]
    rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, OrientedCoreFamily.subgroupOf_map_subtype_self] at hxH
    exact hxH

open scoped Classical in
theorem hasCoherentMap_indFamDetectKer [Fintype G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
        ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M)) := by
  classical
  have hcfg := isPtypeCoreConfig_bot_of_typeIII_IV h₁ h₃ h₅ hG hM htype hc
  have hP := OrientedCoreFamily.isPrimeCyclicTIHyp_commutator hG.odd hc
  obtain ⟨σ, hσ⟩ := hP.exists_isCyclicTIIsometry
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hG.odd hc
  obtain ⟨ω, hω⟩ := (OrientedCoreFamily.isCyclicTIPair_map_subgroupOf hc.le_M_W₁ hc.le_M_W₂
    hW).exists_isCyclicTIIsometry
  set S : Finset (↥M → ℂ) :=
    indFamDetectFinset (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) with hSdef
  have hSc : (S : Set (↥M → ℂ))
      = indFamDetect (commutator ↥M) ((hallCore ↥M).subgroupOf (commutator ↥M)) := by
    rw [hSdef, coe_indFamDetectFinset]
  have hHK : hallCore ↥M ≤ commutator ↥M := by
    rw [← OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc]; exact le_sup_left
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect (σ := σ) (ω := ω)
    (A := ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
    hG.odd hP hσ (OrientedCoreFamily.le_hallCore_subgroupOf_W₂ hc) hHK
    (OrientedCoreFamily.commutator_sdiff_one_conj M) (fun _ _ _ _ hx => ⟨hx.1.1, hx.2⟩)
    (by rw [hcfg.A0_eq]) hcfg.isDadeData
    (OrientedCoreFamily.setOf_conj_eq_of_isCyclicTIPair hc.le_M_W₁ hc.le_M_W₂ hW)
    (OrientedCoreFamily.inter_eq_empty_of_isCyclicTIPair hc.le_M_W₁ hc.le_M_W₂ hW) hω hSc
  have hcore_sub :
      PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M) ⊆ (S : Set (↥M → ℂ)) := by
    rw [hSc]; exact PtypeCoreCoherence.coreDetectFam_subset_indFamDetect M U ⊥
  have hfin : (PtypeCoreCoherence.coreDetectFam M U (⊥ : Subgroup ↥M)).Finite :=
    S.finite_toSet.subset hcore_sub
  have hR' : IsSubcoherent hfin.toFinset (dadeMapFun M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂)
      (CFSG.FeitThompson.Prep06.dadeT M)) R :=
    hR.subset (fun f hf => by
      rw [Set.Finite.mem_toFinset] at hf; exact Finset.mem_coe.1 (hcore_sub hf))
      (fun f hf => by
        rw [Set.Finite.mem_toFinset] at hf ⊢; exact star_mem_coreDetectFam hf)
  obtain ⟨ν, hν⟩ := isCoherent_iff.1 (hcfg.isCoherent_coreDetectFam hR' hfin.coe_toFinset)
  have hsub := indFamDetectKer_subset_coreDetectFam hc
  have hspan := Submodule.span_mono (R := ℤ) hsub
  refine ⟨ν.comp (Submodule.inclusion hspan).toAddMonoidHom, ?_, ?_⟩
  · intro f g
    exact hν.inner_eq _ _
  · intro f hf1
    have hfz : (f : ↥M → ℂ) ∈ charSpanZero (PtypeCoreCoherence.coreDetectFam M U ⊥) :=
      mem_charSpanZero.2 ⟨hspan f.2, hf1⟩
    have h := hν.eq_on_zero ⟨_, hfz⟩
    have h2 := congrArg (fun v : virtualChars G => (v : G → ℂ)) h
    rw [hcfg.coe_baselineMap] at h2
    rw [CFSG.FeitThompson.Prep06.dadeTau_eq]
    exact h2

open scoped Classical in
private theorem twoCoherentLayers_residual
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (_h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G], CFSG.FeitThompson.Prep06.IsMinimalOddSimple G →
      ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
        IsWitnessedPConfiguration M U W₁ W₂ →
        ∀ C : Subgroup G,
          C = U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G) →
        ∀ S₁ S₂ : Set (↥M → ℂ),
          S₁ = CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            ((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔ C : Subgroup G).subgroupOf M) →
          S₂ = CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (C.subgroupOf M) ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M) →
        (Disjoint S₁ S₂ ∧
          S₁ ∪ S₂ = CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (C.subgroupOf M) ∧
          CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂ S₂) := by
  intro G _ _ hG M U W₁ W₂ hM htype hc C hC S₁ S₂ hS₁ hS₂
  classical
  subst hS₁ hS₂
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hHsub : (CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M = hallCore ↥M := by
    rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, OrientedCoreFamily.subgroupOf_map_subtype_self]
  have hUK : U.subgroupOf M ≤ CFSG.FeitThompson.Prep06.derivedOf M := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq,
      ← OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc]
    exact le_sup_right
  have hHK : (CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M ≤ CFSG.FeitThompson.Prep06.derivedOf M := by
    rw [hHsub, CFSG.FeitThompson.Prep06.derivedOf_eq,
      ← OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc]
    exact le_sup_left
  have hCU : C ≤ U := hC ▸ inf_le_left
  have hCM : C ≤ M := hCU.trans hc.le_M_E
  have hCK : C.subgroupOf M ≤ CFSG.FeitThompson.Prep06.derivedOf M :=
    fun x hx => hUK (mem_subgroupOf.2 (hCU (mem_subgroupOf.1 hx)))
  refine ⟨?_, ?_, ?_⟩
  · have hHn : ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M).Normal := by
      rw [hHsub]; exact hallCore_normal
    exact disjoint_indFamKer_sup_indFamDetectKer hHn
  · exact union_indFamKer_sup_indFamDetectKer (CFSG.FeitThompson.Prep06.hallCoreIn_le M) hCM hHK hCK
  · subst hC
    exact hasCoherentMap_indFamDetectKer h₁ h₃ h₅ hG hM htype hc

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

open scoped Classical in
theorem FPF_type_iii_iv_two_coherent_layers
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_two_coherent_layers.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc C hC S₁ S₂ hS₁ hS₂
  obtain ⟨hdisj, hunion, hcoh₂⟩ :=
    twoCoherentLayers_residual h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂ hM htype hc C hC S₁ S₂ hS₁ hS₂
  subst hC
  refine ⟨sup_hallCoreIn_centralizer_eq_commutator_commutator h₂ hG hM htype hc,
    centralizer_eq_commutator_self h₁ hG hM htype hc,
    le_normalizer_centralizer h₅ hG hM htype hc, hdisj, ?_, ?_, hunion, ?_, hcoh₂, ?_, ?_, ?_, ?_⟩
  · rw [hS₁]; exact fun f hf => star_mem_indFamKer hf
  · rw [hS₂]; exact fun f hf => star_mem_indFamDetectKer hf
  · rw [hS₁]; exact hasCoherentMap_layer_one h₂ h₃ h₄ hG hM htype hc
  · rw [hunion]
    exact not_hasCoherentMap_indFamKer_centralizer h₁ h₃ h₄ h₅ hG hM htype hc
  · rw [hS₁]; exact (layer_one_subset_Irr h₂ hG hM htype hc).1
  · rw [hS₁]; exact (layer_one_subset_Irr h₂ hG hM htype hc).2
  · rw [hS₁]; exact exists_card_layer_one h₂ h₅ hG hM htype hc

end CFSG.FeitThompson.Proofs

end
