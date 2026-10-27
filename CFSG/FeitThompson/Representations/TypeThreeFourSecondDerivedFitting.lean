module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.Representations.TypeIIIIVChiefLayerNoncoherence
import CFSG.FeitThompson.Representations.TypeIIIIVProperCoherentIndexBound
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion
public import CFSG.FeitThompson.Representations.QuotientFrobeniusNoncoherentChiefReduction
public import CFSG.FeitThompson.Representations.AbelianizationLayerUniformCoherent
public import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
public import CFSG.FeitThompson.Local.PLengthOneNormalSeries
public import CFSG.FeitThompson.OddOrder.TypeIIIVCoreAbelianizationBound
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
public import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
public import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
public import CFSG.FeitThompson.Local.NormalKernelSectionOrderBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup NormalInducedFamily WeightedFeitExtension CFSG.FeitThompson.Prep05

universe u

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

omit [Finite G] in
theorem subgroupOf_commutator_commutator (M : Subgroup G) :
    (⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆).subgroupOf M
      = ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ := by
  rw [← commutator_subgroupOf_eq (Subgroup.commutator_le_self M), subgroupOf_commutator_self]

omit [Finite G] in
theorem map_subtype_commutator_derivedOf (M : Subgroup G) :
    Subgroup.map M.subtype ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆
      = ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
  rw [Subgroup.map_commutator, CFSG.FeitThompson.Prep06.map_subtype_derivedOf]

omit [Finite G] in
theorem relIndex_commutator_commutator_eq (M : Subgroup G) :
    (⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆).relIndex (⁅M, M⁆ : Subgroup G)
      = (⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆).relIndex
          (CFSG.FeitThompson.Prep06.derivedOf M) := by
  rw [← Subgroup.relIndex_subgroupOf (Subgroup.commutator_le_self M),
    subgroupOf_commutator_commutator, subgroupOf_commutator_self]

theorem commutator_derivedOf_le_fittingRaw (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ ≤ fittingRaw ↥M := by
  refine (Subgroup.map_le_map_iff_of_injective M.subtype_injective).1 ?_
  rw [map_subtype_commutator_derivedOf]
  exact hc.commutator_commutator_le_fittingRaw

theorem relIndex_fittingRaw_derivedOf (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsemi₁ : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (U ⊔ W₁))
    (hsemi₂ : FreeCore.IsInternalSemidirectProduct (U ⊔ W₁) U W₁)
    (hdir : IsInternalDirectProduct (fittingOf M) (hallCoreOf M)
      (centralizerIn U (hallCoreOf M))) :
    (fittingRaw ↥M).relIndex (CFSG.FeitThompson.Prep06.derivedOf M)
      = (centralizerIn U (hallCoreOf M)).relIndex U := by
  have h := Subgroup.relIndex_mul_index (fittingRaw_le_derivedOf hc)
  rw [index_fittingRaw_eq_mul hsemi₁ hsemi₂ hdir, index_derivedOf hc] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h]; ring)

theorem commutator_commutator_lt (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hsolvM : Group.IsSolvable ↥M) :
    ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆
      < CFSG.FeitThompson.Prep06.derivedOf M := by
  refine commutator_lt_self_of_ne_bot (H := CFSG.FeitThompson.Prep06.derivedOf M) fun hbot => ?_
  refine hc.ne_bot_commutator ?_
  rw [← CFSG.FeitThompson.Prep06.map_subtype_derivedOf M, hbot, Subgroup.map_bot]

omit [Finite G] in
theorem no_strict_between_of_isChiefLayer {H₀ : Subgroup G}
    (hlayer : IsChiefLayer M H₀ (hallCoreOf M)) :
    ∀ H₁ : Subgroup G, M ≤ normalizer (H₁ : Set G) →
      ¬ (H₀ < H₁ ∧ H₁ < hallCoreOf M) := by
  intro H₁ hH₁ ⟨hlt₁, hlt₂⟩
  rcases hlayer.2.2 H₁ hH₁ hlt₁.le hlt₂.le with h | h
  · exact hlt₁.ne' h
  · exact hlt₂.ne h

omit [Finite G] in
theorem odd_relIndex_of_odd (hodd : Odd (Nat.card G)) (M : Subgroup G) (D F : Subgroup ↥M) :
    Odd (D.relIndex F) := by
  rw [← natCard_quotient_subgroupOf D F]
  exact odd_natCard_quotient _ (odd_natCard_subgroup (odd_natCard_subgroup hodd M) F)

theorem eq_one_of_bound {a q t : ℕ} (hq : Nat.Prime q) (hqodd : Odd q) (haodd : Odd a)
    (hdvd : q ∣ a - 1) (ht : 1 < t) (hbound : a * t ≤ 2 * q * t + 1) : a = 1 := by
  by_contra hane
  have ha1 : 1 < a := by rcases haodd with ⟨k, hk⟩; omega
  have h2 : 2 ∣ a - 1 := by rcases haodd with ⟨k, hk⟩; omega
  have h2q : 2 * q ∣ a - 1 := (Nat.coprime_two_left.mpr hqodd).mul_dvd_of_dvd_of_dvd h2 hdvd
  have hq1 : 1 < q := hq.one_lt
  have hle : 2 * q ≤ a - 1 := Nat.le_of_dvd (by omega) h2q
  have hmul : (2 * q + 1) * t ≤ a * t := Nat.mul_le_mul_right t (by omega)
  have h3 : 2 * q * t + t ≤ 2 * q * t + 1 :=
    le_trans (le_trans (by ring_nf; omega) hmul) hbound
  omega

theorem dvd_relIndex_sub_one (hW₁ : W₁ ≤ M)
    (hfree : FrobeniusQuotientLayer.FixesOnlyCommutatorCoset (CFSG.FeitThompson.Prep06.derivedOf M)
      (W₁.subgroupOf M))
    (hFK : fittingRaw ↥M ≤ CFSG.FeitThompson.Prep06.derivedOf M) :
    Nat.card ↥W₁ ∣
      (⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆).relIndex
        (fittingRaw ↥M) - 1 := by
  classical
  set K : Subgroup ↥M := CFSG.FeitThompson.Prep06.derivedOf M with hK
  have hKn : K.Normal := by rw [hK, CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  set D : Subgroup ↥M := ⁅K, K⁆ with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  set F : Subgroup ↥M := fittingRaw ↥M with hF
  have hFn : F.Normal := fittingRaw_normal ↥M
  set B : Subgroup ↥M := W₁.subgroupOf M with hB
  have hinv : IsInvariantSubgroup (conjSubgroupAut F B) (D.subgroupOf F) :=
    isInvariantSubgroup_subgroupOf_conjSubgroupAut
  have hcard : Nat.card ↥B = Nat.card ↥W₁ := natCard_subgroupOf_eq_of_le hW₁
  rw [← natCard_quotient_subgroupOf D F, ← hcard]
  refine natCard_dvd_natCard_sub_one_of_mulAut hinv.quotientAut ?_
  intro x hx a hfix
  by_contra ha
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective (s := D.subgroupOf F) x
  rw [hinv.quotientAut_mk, QuotientGroup.eq, mem_subgroupOf] at hfix
  have hu1 : ((a : ↥M))⁻¹ ≠ 1 := by
    intro hcon
    exact ha (Subtype.ext (by simpa using inv_eq_one.1 hcon))
  have hco : ((((conjSubgroupAut F B) a) y : ↥F) : ↥M) = (a : ↥M) * (y : ↥M) * (a : ↥M)⁻¹ :=
    coe_conjSubgroupAut_apply a y
  have hmem : ((y : ↥M))⁻¹ * (((a : ↥M)⁻¹)⁻¹ * (y : ↥M) * ((a : ↥M))⁻¹) ∈ D := by
    have h := D.inv_mem hfix
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hco] at h
    convert h using 1
    group
  have hyD : (y : ↥M) ∈ D :=
    QuotientFrobeniusNoncoherent.mem_commutator_of_fixesOnlyCommutatorCoset hfree
      (B.inv_mem a.2) hu1 (hFK y.2) hmem
  exact hx (by rw [QuotientGroup.eq_one_iff, mem_subgroupOf]; exact hyD)

open scoped Classical in
theorem hasCoherentMap_indFamKer_commutator {G : Type u} [Group G] [Fintype G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂
      (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
        ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆) := by
  classical
  have hfinG : Finite G := Finite.of_fintype G
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hKs : Group.IsSolvable ↥(CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [CFSG.FeitThompson.Prep06.derivedOf_eq]
    have hsolvM : Group.IsSolvable ↥M := hG.solvable M hM.1
    infer_instance
  obtain ⟨hchar, hstar, hstarne, horth, htauC, ⟨R, hR, hRR⟩, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_weighted_normal_family h₁ h₂ G hG M U W₁ W₂ hM htype hc
      _ rfl
  have hfin :
      (CFSG.FeitThompson.Prep06.indFamNonprincipal M (CFSG.FeitThompson.Prep06.derivedOf M)).Finite := by
    rw [← kerLayerIndFam_bot_eq_indFamNonprincipal M]
    exact finite_kerLayerIndFam
  have hsub := isSubcoherent_of_weighted (M := M) (W₁ := W₁) (W₂ := W₂) hfin
    (fun f hf => ⟨(hchar f hf).1, (hchar f hf).2⟩) hstar hstarne horth htauC hR hRR
  have hStar : (hfin.toFinset : Set (↥M → ℂ))
      = kerLayerIndFam (⊥ : Subgroup ↥M) (CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [hfin.coe_toFinset, ← subgroupOf_commutator_self M,
      kerLayerIndFam_bot_eq_indFamNonprincipal M, subgroupOf_commutator_self]
  have hprime : IsPrimeCyclicTIHyp (CFSG.FeitThompson.Prep06.derivedOf M) (W₁.subgroupOf M)
      (W₂.subgroupOf M) := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hfree := hc.fixesOnlyCommutatorCoset_subgroupOf (W₁ := W₁) hG.odd
  have hcoh := QuotientFrobeniusNoncoherent.isCoherent_kerLayerIndFam_commutator_subTauHom
    (E := W₁.subgroupOf M) hsub hStar hprime.mul_eq_univ hfree
  rw [indFamKer_eq_kerLayerIndFam M]
  exact hasCoherentMap_of_isCoherent_subTauHom_of_tau_eq hsub (fun _ => rfl) _ hcoh

theorem fittingRaw_eq_commutator_derivedOf {G : Type u} [Group G] [Finite G]
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) {M U W₁ W₂ : Subgroup G}
    (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    fittingRaw ↥M = ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  have hsolvM : Group.IsSolvable ↥M := hG5.isSolvable_of_ne_top M hM.1
  obtain ⟨-, hq, -, hqodd, -, -, hsemi₁, hsemi₂, -, -, -, hCU, hdir, -, ⟨H₀, hH₀, hlayer⟩, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₃ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  set D : Subgroup ↥M := ⁅CFSG.FeitThompson.Prep06.derivedOf M, CFSG.FeitThompson.Prep06.derivedOf M⁆ with hD
  set F : Subgroup ↥M := fittingRaw ↥M with hF
  set t : ℕ := (centralizerIn U (hallCoreOf M)).relIndex U with ht
  set a : ℕ := D.relIndex F with ha
  have hDF : D ≤ F := commutator_derivedOf_le_fittingRaw hc
  have hsplit : a * t = D.relIndex (CFSG.FeitThompson.Prep06.derivedOf M) := by
    rw [ha, ht, ← relIndex_fittingRaw_derivedOf hc hsemi₁ hsemi₂ hdir]
    exact Subgroup.relIndex_mul_relIndex D F (CFSG.FeitThompson.Prep06.derivedOf M) hDF
      (fittingRaw_le_derivedOf hc)
  have hDlt : D < CFSG.FeitThompson.Prep06.derivedOf M := commutator_commutator_lt hc hsolvM
  have hNM : (⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆) ≤ M :=
    (Subgroup.commutator_le_self _).trans (Subgroup.commutator_le_self M)
  have hDnormal : D.Normal := by rw [hD, CFSG.FeitThompson.Prep06.derivedOf_eq]; infer_instance
  have hNnorm : M ≤ normalizer ((⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ : Subgroup G)
      : Set G) := by
    have : ((⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆).subgroupOf M).Normal := by
      rw [subgroupOf_commutator_commutator]; exact hDnormal
    exact Subgroup.le_normalizer_of_normal_subgroupOf hNM
  have hNlt : (⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆) < (⁅M, M⁆ : Subgroup G) := by
    have h := (Subgroup.map_lt_map_iff_of_injective M.subtype_injective (f := M.subtype)).2 hDlt
    rwa [map_subtype_commutator_derivedOf, CFSG.FeitThompson.Prep06.map_subtype_derivedOf] at h
  have hcohD := hasCoherentMap_indFamKer_commutator h₁ h₂ hG hM htype hc
  have hbound := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_proper_coherent_index_bound h₁ h₂ h₃ G hG
    M U W₁ W₂ hM htype hc H₀ hlayer.1
    (by rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, ← hallCoreOf_eq, ← centralizerIn_eq]; exact hH₀)
    (by rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, ← hallCoreOf_eq]; exact hlayer.2.1)
    (by
      intro H₁ hH₁
      rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, ← hallCoreOf_eq]
      exact no_strict_between_of_isChiefLayer hlayer H₁ hH₁)
    _ hNnorm hNlt
    (by rw [subgroupOf_commutator_commutator]; exact hcohD)
  rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, ← hallCoreOf_eq, ← centralizerIn_eq, ← ht,
    relIndex_commutator_commutator_eq, ← hsplit] at hbound
  have hat : 1 < t := one_lt_relIndex_of_lt hCU
  have haodd : Odd a := odd_relIndex_of_odd hG.odd M D F
  have hdvd : Nat.card ↥W₁ ∣ a - 1 :=
    dvd_relIndex_sub_one hc.le_M_W₁ (hc.fixesOnlyCommutatorCoset_subgroupOf hG.odd)
      (fittingRaw_le_derivedOf hc)
  have ha1 : a = 1 := eq_one_of_bound hq hqodd haodd hdvd hat hbound
  exact le_antisymm (Subgroup.relIndex_eq_one.1 (ha ▸ ha1)) hDF

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_iii_iv_second_derived_fitting
    (h₁ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₂ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₃ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_second_derived_fitting.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  have _ : Finite G := Finite.of_fintype G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hdir, -, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₃ G hG5 M U W₁ W₂ hM htype hc _ _ rfl rfl
  have hH : CFSG.FeitThompson.Prep06.hallCoreIn M = hallCoreOf M := by
    rw [CFSG.FeitThompson.Prep06.hallCoreIn_eq, hallCoreOf_eq]
  have hF : CFSG.FeitThompson.Prep06.fittingIn M = fittingOf M := by
    rw [CFSG.FeitThompson.Prep06.fittingIn_eq, fittingOf_eq]
  rw [hH, hF]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [fittingOf_eq, ← map_subtype_commutator_derivedOf M,
      ← fittingRaw_eq_commutator_derivedOf h₁ h₂ h₃ hG hM htype hc]
  · rw [← centralizerIn_eq]; exact hdir.sup_eq
  · rw [← centralizerIn_eq]; exact hdir.inf_eq_bot
  · rw [← centralizerIn_eq]; exact hdir.commutator_eq_bot

end CFSG.FeitThompson.Proofs

end
