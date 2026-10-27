module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.CommonCoreExcludesRankTwoComplement
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup

universe u

variable {G : Type u} [Group G]

theorem exists_tau_hall_splitting_tau_one_line [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFTAmbient G) {M L E : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L) (hML : M ≠ L)
    (hEM : E ≤ M) (hEne : E ≠ ⊥)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hEL : E ≤ L)
    (hSL : sigmaCore M ⊓ L ≠ ⊥) :
    ∃ E₁ E₂ E₃ : Subgroup G, IsHallPiSubgroupOf (tau1Primes M) E₁ E ∧
      IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E ∧ IsHallPiSubgroupOf (tau3Primes M) E₃ E ∧
      ∃ p ∈ tau1Primes M, ∃ P : Subgroup G, P ≤ E₁ ∧ Nat.card ↥P = p ∧
        E₂ = ⊥ ∧ E₁ ≠ ⊥ ∧ FreeCore.IsInternalSemidirectProduct E E₃ E₁ ∧ P ≤ M ⊓ L ∧
        ∀ Q : Subgroup G, E ≤ normalizer (Q : Set G) → P ≤ normalizer (Q : Set G) := by
  have hGmin := isOddSimpleMinimal_of_isFTAmbient hG
  obtain ⟨E₁, E₂, E₃, hsplit, hE₁of⟩ :=
    FNI_sigma_complement_three_factors h₁ G hGmin M E ⟨hM, hsd⟩
  have hHall₁ : IsHallPiSubgroupOf (tau1Primes M) E₁ E := ⟨hsplit.le_E₁, hsplit.isHall_E₁⟩
  have hHall₂ : IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E := ⟨hsplit.le_E₂, hsplit.isHall_E₂⟩
  have hHall₃ : IsHallPiSubgroupOf (tau3Primes M) E₃ E := ⟨hsplit.le_E₃, hsplit.isHall_E₃⟩
  have hexcl := FTS_common_core_excludes_rank_two_complement h₁ h₂ h₃ h₄ G hG M hM L hL hML E hEM
    hsd hEL hSL
  have hE₂ : E₂ = ⊥ := hexcl.2 E₂ hHall₂
  have hE₁ : E₁ ≠ ⊥ := hE₁of hEne hE₂
  have houter : FreeCore.IsInternalSemidirectProduct E E₃ E₁ := by
    have h := hsplit.outer
    rwa [hE₂, bot_sup_eq] at h
  obtain ⟨p, hpp, hpd⟩ := (Nat.card ↥E₁).exists_prime_and_dvd
    (fun h => hE₁ (Subgroup.card_eq_one.1 h))
  obtain ⟨P, hPE₁, hPcard⟩ := exists_le_natCard_eq_of_prime_dvd hpp hpd
  have hpτ : p ∈ tau1Primes M :=
    isPiSubgroup_iff.1 hHall₁.isPiSubgroup p
      (Nat.mem_primeFactors.2 ⟨hpp, hpd, Nat.card_pos.ne'⟩)
  exact ⟨E₁, E₂, E₃, hHall₁, hHall₂, hHall₃, p, hpτ, P, hPE₁, hPcard, hE₂, hE₁, houter,
    le_inf (hPE₁.trans (hsplit.le_E₁.trans hEM)) (hPE₁.trans (hsplit.le_E₁.trans hEL)),
    fun _ hQ => hPE₁.trans (hsplit.le_E₁.trans hQ)⟩

theorem FTS_common_core_tau_one_witness
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_common_core_tau_one_witness.{u} := by
  intro G _ _ hG M hM L hL hML E hEM hEne hsd hEL hSL
  exact exists_tau_hall_splitting_tau_one_line h₁ h₂ h₃ h₄ hG hM hL hML hEM hEne hsd hEL hSL

end

end CFSG.FeitThompson.Proofs
