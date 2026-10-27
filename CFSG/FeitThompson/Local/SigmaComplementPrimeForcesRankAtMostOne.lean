module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.OutsideSigmaPlaneCoreDisjoint
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
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

theorem elementaryAbelianPRank_inf_le_one_of_dvd_natCard_of_sigmaCore_inf_ne_bot [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G) {M L E : Subgroup G} (hM : IsCoatom M)
    (hL : IsCoatom L) (hML : M ≠ L)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) {p : ℕ} (hp : p.Prime)
    (hpE : p ∣ Nat.card ↥E) (hne : sigmaCore M ⊓ L ≠ ⊥) :
    elementaryAbelianPRank p ↥(M ⊓ L) ≤ 1 := by
  have hdata := FNI_sigma_complement_prime_data h₁ G hG M E ⟨hM, hsd⟩
  have hpσ : p ∉ sigmaPrimes M := by
    have hmem : p ∈ primeDivisorsOf ↥E := ⟨hp, hpE⟩
    rw [hdata.1] at hmem
    exact hmem.2
  by_contra hrank
  obtain ⟨A, hAML, hAiso⟩ :=
    exists_le_nonempty_mulEquiv_of_le_elementaryAbelianPRank (d := 2) hp
      (show 2 ≤ elementaryAbelianPRank p ↥(M ⊓ L) by omega)
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hM, hp, hpσ, hAML.trans inf_le_left, (nonempty_mulEquiv_multiplicative_pi_iff A).1 hAiso⟩
  exact hne (sigmaCore_inf_eq_bot_of_isOutsideSigmaPlane h₁ h₂ h₃ h₄ hG hosp hL hML.symm
    (hAML.trans inf_le_right))

theorem FBG_sigma_intersection_outside_prime_rank_one
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_intersection_outside_prime_rank_one.{u} := by
  intro G _ _ hG M L hM hL hML E hsd p hp hpE hne
  have _ : Finite G := Finite.of_fintype G
  exact elementaryAbelianPRank_inf_le_one_of_dvd_natCard_of_sigmaCore_inf_ne_bot h₁ h₂ h₃ h₄
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
    hM hL hML hsd hp hpE hne

end

end CFSG.FeitThompson.Proofs
