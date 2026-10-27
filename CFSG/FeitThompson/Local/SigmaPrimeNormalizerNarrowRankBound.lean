module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeForcesRankAtMostOne
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerCommonFactor
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideNarrowPrimeFactor
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem factorization_natCard_eq_of_coe_eq_mul [Finite G] {p : ℕ} {T D J : Subgroup G}
    (hT : (T : Set G) = (D : Set G) * (J : Set G)) (hpD : ¬ p ∣ Nat.card ↥D) :
    (Nat.card ↥T).factorization p = (Nat.card ↥J).factorization p := by
  have key := natCard_mul_mul_natCard_inf D J
  rw [← hT] at key
  have hTcard : Nat.card ↑(T : Set G) = Nat.card ↥T := rfl
  rw [hTcard] at key
  have hpinf : ¬ p ∣ Nat.card ↥(D ⊓ J) := fun h =>
    hpD (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hz1 : (Nat.card ↥(D ⊓ J)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpinf
  have hz2 : (Nat.card ↥D).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpD
  have h1 : (Nat.card ↥T * Nat.card ↥(D ⊓ J)).factorization p
      = (Nat.card ↥D * Nat.card ↥J).factorization p := by rw [key]
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Finsupp.add_apply, hz1, hz2, add_zero, zero_add] at h1
  exact h1

theorem elementaryAbelianPRank_le_of_factorization_eq [Finite G] {p : ℕ} (hp : p.Prime)
    {T J : Subgroup G} (hJT : J ≤ T)
    (hfac : (Nat.card ↥T).factorization p = (Nat.card ↥J).factorization p)
    {n : ℕ} (hrank : elementaryAbelianPRank p ↥J ≤ n) :
    elementaryAbelianPRank p ↥T ≤ n := by
  have := Fact.mk hp
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥J))
  have hPJ : (P0 : Subgroup ↥J).map J.subtype ≤ J := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥((P0 : Subgroup ↥J).map J.subtype)
      = p ^ (Nat.card ↥J).factorization p := by
    rw [Subgroup.card_subtype]; exact P0.card_eq_multiplicity
  have hsyl : _root_.CFSG.FeitThompson.IsSylowIn p T ((P0 : Subgroup ↥J).map J.subtype) :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp (hPJ.trans hJT)).2 (by rw [hPcard, hfac])
  calc elementaryAbelianPRank p ↥T
      = elementaryAbelianPRank p ↥((P0 : Subgroup ↥J).map J.subtype) :=
        (elementaryAbelianPRank_eq_of_isSylowSubgroupOf hp hsyl).symm
    _ ≤ elementaryAbelianPRank p ↥J := elementaryAbelianPRank_le_of_le hp.one_lt hPJ
    _ ≤ n := hrank

theorem exists_conj_le_sigmaCore [Finite G] {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hHall : IsHallPiSubgroup (sigmaPrimes M) (sigmaCore M)) (hqM : q ∈ sigmaPrimes M)
    {Y : Subgroup G} (hYq : IsPGroup q ↥Y) :
    ∃ g : G, Y ≤ sigmaCore (MulAut.conj g • M) := by
  have := Fact.mk hq
  obtain ⟨Q0⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥(sigmaCore M)))
  have hQS : (Q0 : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype ≤ sigmaCore M :=
    Subgroup.map_subtype_le _
  have hQcard : Nat.card ↥((Q0 : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype)
      = q ^ (Nat.card ↥(sigmaCore M)).factorization q := by
    rw [Subgroup.card_subtype]; exact Q0.card_eq_multiplicity
  have hidx : ¬ q ∣ (sigmaCore M).index := fun hd =>
    hHall.notMem_of_mem_primeFactors_index q
      (Nat.mem_primeFactors.2 ⟨hq, hd, Subgroup.index_ne_zero_of_finite⟩) hqM
  have hfac : (Nat.card ↥(sigmaCore M)).factorization q = (Nat.card G).factorization q := by
    have hmul : Nat.card ↥(sigmaCore M) * (sigmaCore M).index = Nat.card G :=
      Subgroup.card_mul_index _
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup (hQcard.trans (by rw [hfac])) hYq
  refine ⟨g, hg.trans ?_⟩
  rw [sigmaCore_conj_smul]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hQS

theorem elementaryAbelianPRank_inf_normalizer_le_one_of_le_sigmaCore [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsOddOrderMinimalSimple G) {M L E Y : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L)
    (hML : M ≠ L) (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    {p : ℕ} (hp : p.Prime) (hpE : p ∣ Nat.card ↥E) (hpβ : p ∉ betaPrimes G)
    {q : ℕ} (hq : q.Prime) (hqM : q ∈ sigmaPrimes M)
    (hYL : Y ≤ L) (hY : Y ≠ ⊥) (hYq : IsPGroup q ↥Y) (hYS : Y ≤ sigmaCore M) :
    elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G)) ≤ 1 := by
  let _ : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hYM : Y ≤ M := hYS.trans (sigmaCore_le M)
  by_cases hNM : normalizer (Y : Set G) ≤ M
  ·
    have hne : sigmaCore M ⊓ L ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ le_inf hYS hYL))
    have hrank : elementaryAbelianPRank p ↥(M ⊓ L) ≤ 1 :=
      FBG_sigma_intersection_outside_prime_rank_one h₁ h₆ h₇ h₈ G hG M L hM hL hML E hE p hp hpE hne
    exact le_trans (elementaryAbelianPRank_le_of_le hp.one_lt
      (le_inf (le_trans inf_le_right hNM) inf_le_left)) hrank
  ·
    have hNtop : normalizer (Y : Set G) ≠ ⊤ :=
      (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hY hYq).ne
    obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top hNtop
    have hMT : M ≠ T := fun h => hNM (h ▸ hNT)
    have hYT : Y ≤ T := Subgroup.le_normalizer.trans hNT
    have hneT : sigmaCore M ⊓ T ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ le_inf hYS hYT))
    have hrankJ : elementaryAbelianPRank p ↥(M ⊓ T) ≤ 1 :=
      FBG_sigma_intersection_outside_prime_rank_one h₁ h₆ h₇ h₈ G hG M T hM hT hMT E hE p hp hpE
        hneT
    have hfac : ∃ D : Subgroup G, ¬ p ∣ Nat.card ↥D ∧
        (T : Set G) = (D : Set G) * ((M ⊓ T : Subgroup G) : Set G) := by
      by_cases hqT : q ∈ sigmaPrimes T
      · obtain ⟨-, hpD, hprod⟩ := FBG_sigma_prime_normalizer_common_sigma_prime_factor h₁ h₇ h₈ G
          hG M T hM hT hMT q hq hqM Y hYM hY hYq hNT E hE p hp hpE hpβ hqT
          (pComplCoreIn p (⁅T, T⁆ : Subgroup G)) rfl
        exact ⟨_, hpD, hprod⟩
      · obtain ⟨-, hpD, hsdT⟩ := FBG_sigma_prime_normalizer_outside_narrow_prime_factor h₁ h₂ h₃ h₄
          h₅ h₆ h₇ G hG M T hM hT hMT q hq hqM Y hYM hY hYq hNT E hE p hp hpE hpβ hqT
        refine ⟨sigmaCore T, hpD, ?_⟩
        have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (sigmaCore T) (M ⊓ T)
          (le_trans inf_le_right hsdT.le_normalizer)
        rwa [hsdT.sup_eq] at hcoe
    obtain ⟨D, hpD, hprod⟩ := hfac
    have hrankT : elementaryAbelianPRank p ↥T ≤ 1 :=
      elementaryAbelianPRank_le_of_factorization_eq hp inf_le_right
        (factorization_natCard_eq_of_coe_eq_mul hprod hpD) hrankJ
    exact le_trans (elementaryAbelianPRank_le_of_le hp.one_lt
      (le_trans inf_le_right hNT)) hrankT

theorem elementaryAbelianPRank_inf_normalizer_le_one [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsOddOrderMinimalSimple G) {M L E Y : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L)
    (hnc : ∀ g : G, L ≠ conjSubgroup M g)
    (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    {p : ℕ} (hp : p.Prime) (hpE : p ∣ Nat.card ↥E) (hpβ : p ∉ betaPrimes G)
    {q : ℕ} (hq : q.Prime) (hqM : q ∈ sigmaPrimes M)
    (hYL : Y ≤ L) (hY : Y ≠ ⊥) (hYq : IsPGroup q ↥Y) :
    elementaryAbelianPRank p ↥(L ⊓ normalizer (Y : Set G)) ≤ 1 := by
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨-, hHall, -⟩ := h₁ G hG M hM
  obtain ⟨g, hYS⟩ := exists_conj_le_sigmaCore hq hHall hqM hYq
  refine elementaryAbelianPRank_inf_normalizer_le_one_of_le_sigmaCore h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG
    (E := MulAut.conj g • E) (isCoatom_conj_smul hM g) hL ?_ ?_ hp ?_ hpβ hq ?_ hYL hY hYq hYS
  ·
    exact fun h => hnc g⁻¹ (by rw [← h, conjSubgroup_eq, inv_inv, coe_conj_smul_eq_map])
  · rw [sigmaCore_conj_smul]
    exact isInternalSemidirectProduct_conj_smul hE g
  · rwa [natCard_conj_smul]
  · rwa [sigmaPrimes_conj_smul]

theorem FBG_sigma_prime_normalizer_narrow_rank_bound
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_prime_normalizer_narrow_rank_bound.{u} := by
  intro G _ _ hG M L hM hL hnc E hE p hp hpE hpβ q hq hqM Y hYL hY hYq
  have _ : Finite G := Finite.of_fintype G
  exact elementaryAbelianPRank_inf_normalizer_le_one h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG hM hL hnc hE hp
    hpE hpβ hq hqM hYL hY hYq

end

end CFSG.FeitThompson.Proofs
