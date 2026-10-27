module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
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

variable {G : Type*} [Group G]

theorem isPlane_of_isElementaryAbelianPlane {p : ℕ} {A : Subgroup G}
    (h : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p A) : Prep03.IsPlane p A := h

theorem isAmbient_of_isOddOrderMinimalSimple [Fintype G] (hG : IsOddOrderMinimalSimple G) :
    Prep03.IsAmbient G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

theorem isSemidirect_of_isInternalSemidirectProduct {X Y Z : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct X Y Z) : Prep03.IsSemidirect X Y Z :=
  ⟨h.left_le, h.right_le, h.le_normalizer, h.sup_eq, h.inf_eq_bot⟩

theorem FBG_tau_two_ambient_abelian_propagation
    (_h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_tau_two_ambient_abelian_propagation.{u} := by
  intro G _ _ hG M hM E hdecomp p hp hpab q hq R
  have hamb : Prep03.IsAmbient G := isAmbient_of_isOddOrderMinimalSimple hG
  have hqp : q.Prime := prime_of_mem_tauTwoPrimes hq
  have : Fact q.Prime := ⟨hqp⟩
  by_contra hnonab
  obtain ⟨B, hBE, hBplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hq hdecomp
  have hsetup : Prep03.IsPlaneSetup G q M B E :=
    ⟨hamb, hM, hqp, notMem_sigmaPrimes_of_mem_tauTwoPrimes hq,
      hBE.trans hdecomp.right_le, isPlane_of_isElementaryAbelianPlane hBplane,
      isSemidirect_of_isInternalSemidirectProduct hdecomp, hBE⟩
  have hnonab' : ∃ Q : Subgroup G, Prep03.IsSylowTop q Q ∧ ¬ IsMulCommutative ↥Q :=
    ⟨(R : Subgroup G), R.card_eq_multiplicity, hnonab⟩
  have hsing : tauTwoPrimes M = {q} :=
    FNI_nonabelian_ambient_single_rank_two_prime h₂ h₃ h₄ h₅ G hamb q M B E hsetup hnonab'
  have hpq : p = q := Set.mem_singleton_iff.1 (hsing ▸ hp)
  subst hpq
  exact hnonab (hpab R)

end

end CFSG.FeitThompson.Proofs
