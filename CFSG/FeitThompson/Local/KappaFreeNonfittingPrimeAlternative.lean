module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.KappaFreeNonfittingPlaneTransfer
import CFSG.FeitThompson.Local.TauTwoSubgroupCentralizerUnique
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.KappaNormalizerReflection
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem mem_kappaPrimes_of_mem_tau1Primes [Finite G] (hodd : Odd (Nat.card G)) {q : ℕ}
    {T X : Subgroup G} (hq : q ∈ tau1Primes T) (hXT : X ≤ T) (hXcard : Nat.card ↥X = q)
    (hcent : sigmaCore T ⊓ centralizer (X : Set G) ≠ ⊥) : q ∈ kappaPrimes T := by
  obtain ⟨hqp, hqT, hqσ, hqrank, -⟩ := mem_tau1Primes_iff.1 hq
  have hqodd : Odd q := hodd.of_dvd_nat (hqT.trans (Subgroup.card_subgroup_dvd_card T))
  have hcyc := exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one T hqp hqodd hqrank.le
  exact (mem_kappaPrimes_iff_inf_centralizer_ne_bot hqp hqσ hcyc hXT hXcard).2 hcent

theorem FTS_kappa_free_nonfitting_prime_alternative
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_plane_action.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_nonfitting_prime_alternative.{u} := by
  intro G _ _ hG q M E Q hcfg
  obtain ⟨p, hp, hpq, hτ₂, A, hAE, hAplane, -, hD, hDcard, hAQ, hCAQ, -⟩ :=
    h₇ G hG q M E Q hcfg
  obtain ⟨htrans, T, hT, hNT⟩ :=
    FTS_kappa_free_nonfitting_plane_transfer h₁ h₂ h₄ h₅ h₆ h₈ G hG q M E Q hcfg p A hp hpq hτ₂
      hAE hAplane hD hDcard hAQ hCAQ
  obtain ⟨hpσT, hpβT, hqτ, hQT, hcentT⟩ := htrans T hT hNT
  have hTc : IsCoatom T := hT
  have hQbot : Q ≠ ⊥ := by
    intro h
    refine hcfg.prime.ne_one ?_
    rw [← hcfg.natCard_Q, h]
    simp
  refine ⟨T, hT, ?_⟩
  rcases hqτ with hq1 | hq2
  ·
    right
    have hqκ : q ∈ kappaPrimes T :=
      mem_kappaPrimes_of_mem_tau1Primes hG.odd_natCard hq1 hQT hcfg.natCard_Q hcentT
    refine ⟨hqκ, hQT, fun L hL => ?_⟩
    have hne : sigmaPrimes T ≠ betaPrimes ↥T := fun heq => hpβT (heq ▸ hpσT)
    exact isInternalSemidirectProduct_sigmaCore_of_sigmaPrimes_ne_betaPrimes
      (FBG_kappa_nontrivial_complement_structure h₁ h₃ h₆ h₈ h₉) h₃
      hG.odd_natCard hG.isSimpleGroup hG.not_isMulCommutative hG.isSolvable hTc ⟨q, hqκ⟩ hne hL
  ·
    left
    refine ⟨hq2, hQT, ?_⟩
    have hprimes : ∀ s ∈ (Nat.card ↥Q).primeFactors, s ∈ tauTwoPrimes T := by
      intro s hs
      rw [hcfg.natCard_Q, hcfg.prime.primeFactors] at hs
      simpa [Finset.mem_singleton.1 hs] using hq2
    exact (FTS_tau_two_subgroup_centralizer_unique h₂ h₅ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
      T hTc Q hQT hQbot hprimes hcentT).2

end

end CFSG.FeitThompson.Proofs
