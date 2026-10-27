module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonabelianCommonOvergroupSylow
import CFSG.FeitThompson.Local.SharedRankTwoMaximaContradiction
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
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

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_nonabelian_prime_subgroup_unique_maximum
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u} := by
  intro G _ _ hG p a P hp ha hPcard hPna
  have := hG.isSimpleGroup
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
  have hPne : P ≠ ⊥ := by
    rintro rfl
    exact hPna (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  have hPlt : P < ⊤ := lt_top_of_isPGroup hG.not_isMulCommutative hp hPne hPp
  obtain ⟨M, hM, hPM⟩ := exists_isCoatom_ge_of_ne_top hPlt.ne
  refine ⟨M, ⟨hM, hPM⟩, ?_⟩
  rintro T ⟨hT, hPT⟩
  by_contra hne
  have hpodd : Odd p := hp.odd_of_ne_two (by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2
      ((hPcard ▸ dvd_pow_self 2 (by omega : a ≠ 0)).trans P.card_subgroup_dvd_card)))
  obtain ⟨-, ⟨R, hRna, -, hRTM, -, -, hRG, hNR, hrank⟩, -, -⟩ :=
    FNI_nonabelian_common_overgroup_sylow h₁ h₂ h₅ G hG p T M P hT hM hne hp
      (le_inf hPT hPM) hPp hPna
  exact hne (FNI_shared_rank_two_maxima_contradiction h₁ h₂ h₃ h₄ h₆ G hG p T M R hT hM hne hp
    hpodd hRTM.le hRna hRG hrank hNR)

end

end CFSG.FeitThompson.Proofs
