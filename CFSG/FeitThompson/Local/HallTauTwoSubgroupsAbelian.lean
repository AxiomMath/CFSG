module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.TauTwoFullCentralHall
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormalizer
import CFSG.FeitThompson.Local.CommonCoreExcludesRankTwoComplement
import CFSG.FeitThompson.Local.TauTwoAbelianSylowPropagation
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
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

variable {G : Type u} [Group G]

theorem isMulCommutative_of_isHallPiSubgroupOf_tauTwoPrimes
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    [Finite G] (hG : IsOddOrderMinimalSimple G) {M E E₂ : Subgroup G} (hM : IsCoatom M)
    (hdecomp : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (hE₂ : IsHallPiSubgroupOf (tauTwoPrimes M) E₂ E) : IsMulCommutative ↥E₂ := by
  let _inst : Fintype G := Fintype.ofFinite G
  have hG' : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  rcases Set.eq_empty_or_nonempty (tauTwoPrimes M) with hτ | ⟨p, hp⟩
  · have hbot : E₂ = ⊥ := eq_bot_of_isHallPiSubgroupOf_empty (hτ ▸ hE₂)
    subst hbot
    infer_instance
  · have hpp : p.Prime := prime_of_mem_tauTwoPrimes hp
    have : Fact p.Prime := ⟨hpp⟩
    by_cases hpab : ∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G)
    · exact (FBG_tau_two_full_central_hall h₁ h₂ h₃ h₄ h₅ G hG M hM E hdecomp p hp hpab E₂ hE₂).2.1
    · obtain ⟨R, hR⟩ := not_forall.1 hpab
      obtain ⟨A, hAE, hAplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hp hdecomp
      have hAM : A ≤ M := hAE.trans hdecomp.right_le
      have hosA : IsOutsideSigmaPlane p M A :=
        ⟨hM, hpp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hp, hAM, hAplane⟩
      have hamb : Prep03.IsAmbient G :=
        ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
      have hsetup : Prep03.IsPlaneSetup G p M A E :=
        ⟨hamb, hM, hpp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hp, hAM, hAplane,
          isSemidirect_of_isInternalSemidirectProduct hdecomp, hAE⟩
      have hτeq : tauTwoPrimes M = {p} :=
        FNI_nonabelian_ambient_single_rank_two_prime h₂ h₃ h₄ h₅ G hamb p M A E hsetup
          ⟨(R : Subgroup G), R.card_eq_multiplicity, hR⟩
      have hE₂pg : IsPGroup p ↥E₂ :=
        (isPiSubgroup_singleton_iff hpp E₂).1 (hτeq ▸ hE₂.isPiSubgroup)
      obtain ⟨P, hP, hE₂P⟩ :=
        exists_isSylowSubgroupOf_ge_of_isPGroup (hE₂.le.trans hdecomp.right_le) hE₂pg
      have hPab : IsMulCommutative ↥P := ((h₃ G hG' p M A hosA).2.2.1 P hP).1
      exact isMulCommutative_of_le hE₂P

theorem FBG_tau_two_hall_abelian
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (_h₅ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (_h₆ : _root_.CFSG.FeitThompson.Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u} :=
  fun _G _ _ hG _M hM _E hdecomp _E₂ hE₂ =>
    isMulCommutative_of_isHallPiSubgroupOf_tauTwoPrimes h₁ h₂ h₃ h₄ h₇ hG hM hdecomp hE₂

end

end CFSG.FeitThompson.Proofs
