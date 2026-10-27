module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.OutsideSigmaPlaneCoreDisjoint
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
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

theorem isOddSimpleMinimal_of_isFTAmbient [Finite G] (hG : IsFTAmbient G) :
    _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩

theorem eq_bot_of_isHallPiSubgroupOf_empty [Finite G] {E₂ E : Subgroup G}
    (h : IsHallPiSubgroupOf (∅ : Set ℕ) E₂ E) : E₂ = ⊥ := by
  have hpf : (Nat.card ↥(E₂.subgroupOf E)).primeFactors = ∅ :=
    Finset.eq_empty_iff_forall_notMem.2 fun q hq => isPiSubgroup_iff.1 h.2.isPiSubgroup q hq
  have hcard : Nat.card ↥(E₂.subgroupOf E) = 1 := by
    rcases Nat.primeFactors_eq_empty.1 hpf with h0 | h1
    · exact absurd h0 Nat.card_pos.ne'
    · exact h1
  exact (Subgroup.subgroupOf_eq_bot.1 (Subgroup.card_eq_one.1 hcard)).eq_bot_of_le h.1

theorem tauTwoPrimes_eq_empty_of_sigmaCore_inf_ne_bot [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFTAmbient G) {M L E : Subgroup G} (hM : IsCoatom M) (hL : IsCoatom L) (hML : M ≠ L)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) (hEL : E ≤ L)
    (hSL : sigmaCore M ⊓ L ≠ ⊥) : tauTwoPrimes M = ∅ := by
  have hGmin := isOddSimpleMinimal_of_isFTAmbient hG
  have hEM : E ≤ M := hsd.right_le
  obtain ⟨hπE, hrank, -⟩ := FNI_sigma_complement_prime_data h₁ G hGmin M E ⟨hM, hsd⟩
  refine Set.eq_empty_iff_forall_notMem.2 fun p hp => ?_
  obtain ⟨hpprime, hpσ, hpM⟩ := mem_tauTwoPrimes_iff.1 hp
  have hpdvdM : p ∣ Nat.card ↥M := (one_le_elementaryAbelianPRank_iff hpprime).1 (by omega)
  have hpE : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E := by
    rw [hπE]; exact ⟨⟨hpprime, hpdvdM⟩, hpσ⟩
  have hrE : elementaryAbelianPRank p ↥E = 2 := (hrank p hpE).1.trans hpM
  obtain ⟨A, hAE, hAplane⟩ := exists_isElementaryAbelianPlane_le hpprime hrE.ge
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hM, hpprime, hpσ, hAE.trans hEM, hAplane⟩
  exact hSL (FNI_outside_sigma_plane_core_disjoint h₁ h₂ h₃ h₄ G hGmin p M A L hosp hL
    (Ne.symm hML) (hAE.trans hEL))

theorem FTS_common_core_excludes_rank_two_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_common_core_excludes_rank_two_complement.{u} := by
  intro G _ _ hG M hM L hL hML E _ hsd hEL hSL
  have hτ := tauTwoPrimes_eq_empty_of_sigmaCore_inf_ne_bot h₁ h₂ h₃ h₄ hG hM hL hML hsd hEL hSL
  exact ⟨hτ, fun E₂ hE₂ => eq_bot_of_isHallPiSubgroupOf_empty (hτ ▸ hE₂)⟩

end

end CFSG.FeitThompson.Proofs
