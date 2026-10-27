module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneMaximalOvergroups
import CFSG.FeitThompson.Local.PlaneNormalizerOverlapFrattini
import CFSG.FeitThompson.Local.OutsideSigmaPlanePrimesTauOneOrTwo
import CFSG.FeitThompson.Local.PlaneNormalizerRankTwoPrimesInSigma
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormalizer
import CFSG.FeitThompson.Local.OutsideSigmaNormalizerRankTwoPlane
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
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

open Pointwise CFSG.FeitThompson CFSG.FeitThompson
  Subgroup

universe u

theorem FNI_plane_normalizer_overlap_prime_maximum
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_prime_maximum.{u} := by
  intro G _ _ hG p M A E T hosp hsc hAE hT hNT q hq hqidx hqcard Q₀ hQ₀ hQ₀card
  have hsimple := hG.isSimpleGroup
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hqfact := Fact.mk hq
  have hQ₀bot : Q₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hQ₀card
    exact hq.one_lt.ne hQ₀card
  have hQ₀p : IsPGroup q Q₀ := IsPGroup.of_card (n := 1) (by rw [hQ₀card, pow_one])
  have hNQlt : normalizer (Q₀ : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hQ₀bot hQ₀p
  obtain ⟨L, hL, hNQL⟩ := exists_isCoatom_ge_of_ne_top hNQlt.ne
  have hAcQ : A ≤ centralizer (Q₀ : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hQ₀ hy)).2) x hx).symm
  have hAL : A ≤ L := (hAcQ.trans (Subgroup.centralizer_le_normalizer _)).trans hNQL
  have hplane8 : Prep08.IsPlaneAt p A :=
    ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.2
      hosp.isElementaryAbelianPlane.isElementaryAbelianSubgroup,
      hosp.isElementaryAbelianPlane.natCard'⟩
  have hCL : centralizer (A : Set G) ≤ L :=
    (FTS_plane_maximal_overgroups h₁ h₆ h₇ h₉ G hG8 L A p hL hosp.prime hAL hplane8).1
  obtain ⟨Q, hQsyl, hQ₀Q⟩ :=
    exists_isSylowSubgroupOf_ge_of_isPGroup (hQ₀.trans inf_le_left) hQ₀p
  obtain ⟨-, -, -, -, -, -, hfrat⟩ :=
    FNI_plane_normalizer_overlap_frattini h₁ h₂ h₃ h₅ G hG p M A E T hosp hsc hAE hT hNT q hq
      hqidx hqcard Q₀ Q hQ₀ hQ₀card hQsyl hQ₀Q
  have hNAL : normalizer (A : Set G) ≤ L := by
    intro x hx
    have hx' : x ∈ ((normalizer (A : Set G) : Subgroup G) : Set G) := hx
    rw [hfrat] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact mul_mem (hCL ha) (hNQL (Subgroup.mem_inf.1 hb).2)
  have htransfer := FNI_plane_normalizer_action_prime_transfer h₁ h₂ h₃ h₄ h₅ h₈ G hG p M A E L
    hosp hsc hAE hL hNAL q hq hqidx
  have hqσL : q ∉ sigmaPrimes L := by
    rcases htransfer with h | h
    · exact notMem_sigmaPrimes_of_mem_tau1Primes h
    · exact notMem_sigmaPrimes_of_mem_tauTwoPrimes h
  have hrankL : elementaryAbelianPRank q ↥L = 2 :=
    elementaryAbelianPRank_eq_two_of_notMem_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hL hq hqσL hQ₀card hNQL
  have hqτ₂L : q ∈ tauTwoPrimes L := mem_tauTwoPrimes_iff.2 ⟨hq, hqσL, hrankL⟩
  obtain ⟨B, hBL, hBplane⟩ := exists_isPlaneAt_le_of_elementaryAbelianPRank_eq_two hq hrankL
  have hnil : Group.IsNilpotent ↥(sigmaCore L) := (h₈ G hG8 L B q hL hq hqσL hBL hBplane).1
  have hpτ₂M : p ∈ tauTwoPrimes M :=
    mem_tauTwoPrimes_iff.2 ⟨hosp.prime, hosp.notMem_sigmaPrimes, (h₅ G hG p M A hosp).1⟩
  have hpL : p ∈ sigmaPrimes L :=
    (FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₃ h₄ h₅ h₈ G hG p M A E L hosp hsc hAE
      hL hNAL).2 hpτ₂M
  have hpT : p ∈ sigmaPrimes T :=
    (FNI_plane_normalizer_rank_two_primes_in_sigma h₁ h₂ h₃ h₄ h₅ h₈ G hG p M A E T hosp hsc hAE
      hT hNT).2 hpτ₂M
  have hAT : A ≤ T := le_normalizer.trans hNT
  have hApg : IsPGroup p ↥A := IsPGroup.of_card hosp.isElementaryAbelianPlane.natCard'
  have hconj : ∃ g : G, T = Prep08.conjSubgroup L g := by
    by_contra hcon
    push Not at hcon
    have hsep := (FTS_nilpotent_sigma_prime_separation G hG8 L T hL hT hcon hnil).1
    exact Set.notMem_empty p (hsep ▸ (⟨hpL, hpT⟩ : p ∈ sigmaPrimes L ∩ sigmaPrimes T))
  obtain ⟨g, hg⟩ := hconj
  have hTL : T = MulAut.conj g⁻¹ • L := hg
  have hLT : L = T := by
    have hA1 : A ≤ MulAut.conj (1 : G) • L := by simpa using hAL
    have hA2 : A ≤ MulAut.conj g⁻¹ • L := hTL ▸ hAT
    obtain ⟨c, hc, hceq⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes
      hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hL hpL hApg hA1 hA2
    rw [map_one, one_smul] at hceq
    have hcT : c ∈ T := hNT (Subgroup.centralizer_le_normalizer _ hc)
    have hcL : MulAut.conj c • L = T := by rw [hceq, ← hTL]
    have hLc : L = MulAut.conj c⁻¹ • T := by rw [← hcL, map_inv, inv_smul_smul]
    rw [hLc, Subgroup.conj_smul_eq_self_of_mem (inv_mem hcT)]
  rw [hLT] at hqτ₂L hNQL
  exact ⟨hqτ₂L, hNQL⟩

end

end CFSG.FeitThompson.Proofs
