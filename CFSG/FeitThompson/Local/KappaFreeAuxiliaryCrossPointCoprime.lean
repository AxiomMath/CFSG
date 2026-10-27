module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaFreeAuxiliaryOverlapExcludesTauTwo
import CFSG.FeitThompson.Local.KappaFreeTauTwoFreeFrobenius
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

theorem FTS_kappa_free_auxiliary_cross_point_coprimality
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_kappa_free_auxiliary_cross_point_coprimality.{u} := by
  intro G _ _ hG M hM T hT hτ hβ hκ hσ hx b hbM hb1 hCb
  have hST : ∀ p ∈ (Nat.card ↥(sigmaCore T)).primeFactors, p ∈ sigmaPrimes T :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T)
  have hcardT : Nat.card ↥(sigmaCore T) ≠ 0 := Nat.card_pos.ne'
  have hCbM : Nat.card ↥(M ⊓ centralizer ({b} : Set G)) ∣ Nat.card ↥M :=
    Subgroup.card_dvd_of_le inf_le_left
  by_cases hov : ∃ r : ℕ, r ∣ Nat.card ↥M ∧ r ∈ sigmaPrimes T
  ·
    have hτ2 : tauTwoPrimes M = ∅ :=
      FTS_kappa_free_auxiliary_overlap_excludes_tau_two h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
        G hG M hM T hT hτ hβ hκ hσ hx hov
    obtain ⟨-, ⟨E, -, -, hsd, hfree⟩, -⟩ :=
      FTS_kappa_free_tau_two_free_frobenius h₁ G hG M hM hκ hτ2
    have hbS : b ∈ sigmaCore M := by
      by_contra hbS
      exact hCb (inf_centralizer_singleton_eq_bot_of_mem_of_notMem hsd.coe_eq_mul.symm
        hsd.inf_eq_bot hfree hbM hbS)
    have hle : M ⊓ centralizer ({b} : Set G) ≤ sigmaCore M :=
      inf_centralizer_singleton_le_of_mem_of_ne_one hsd.coe_eq_mul.symm hsd.inf_eq_bot hfree
        hbS hb1
    have hSM : ∀ p ∈ (Nat.card ↥(sigmaCore M)).primeFactors, p ∈ sigmaPrimes M :=
      isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M)
    refine Nat.coprime_of_dvd fun p hp hpT hpC => ?_
    have hpσT : p ∈ sigmaPrimes T := hST p (Nat.mem_primeFactors.2 ⟨hp, hpT, hcardT⟩)
    have hpσM : p ∈ sigmaPrimes M :=
      hSM p (Nat.mem_primeFactors.2
        ⟨hp, hpC.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
    have hmem : p ∈ sigmaPrimes M ∩ sigmaPrimes T := ⟨hpσM, hpσT⟩
    rw [hσ] at hmem
    exact hmem
  ·
    refine Nat.coprime_of_dvd fun p hp hpT hpC => ?_
    exact hov ⟨p, hpC.trans hCbM, hST p (Nat.mem_primeFactors.2 ⟨hp, hpT, hcardT⟩)⟩

end

end CFSG.FeitThompson.Proofs
