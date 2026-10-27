module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.ResidualComplementNilpotentCore
import CFSG.FeitThompson.Local.AbelianAmbientNormalHallInertiaExponent
import CFSG.FeitThompson.Local.NonabelianAmbientNormalHallFreeComplement
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.TauTwoAbelianSylowPropagation
import CFSG.FeitThompson.Local.KappaResidualComplementNormalizerEscape
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

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson

universe u

theorem FBG_local_inertia_and_exponent_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_abelian_normal_hall_full_exponent_cycle.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_prime_kernel_complement.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_local_inertia_and_exponent_complement.{u} := by
  classical
  intro G _ _ hG M K U hsetup hU
  let _ : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hGamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  set E : Subgroup G := U ⊔ K with hEdef
  have hKM : IsHallPiSubgroupOf (kappaPrimes M) K M := ⟨hsetup.le_M_K, hsetup.hall_K⟩
  have hKhall : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    _root_.CFSG.FeitThompson.Proofs.isHallPiOf_of_isHallPiSubgroupOf hKM
  have hdecomp : Prep03.IsSemidirect M (sigmaCore M) E :=
    _root_.CFSG.FeitThompson.Proofs.isSemidirect_of_isInternalSemidirectProduct hsetup.semidirect_M
  have hdecompE : Prep03.IsSemidirect E U K :=
    _root_.CFSG.FeitThompson.Proofs.isSemidirect_of_isInternalSemidirectProduct hsetup.semidirect_UK
  have hEM : E ≤ M := hsetup.semidirect_M.right_le
  obtain ⟨-, heq, -⟩ :=
    (FBG_residual_complement_nilpotent_core h₁ h₅ h₇ G hGmin M hsetup.isCoatom K U hKM
      hsetup.le_M_U hsetup.semidirect_M hsetup.semidirect_UK).1 hU
  refine ⟨heq, ?_⟩
  by_cases hab : ∀ p ∈ tauTwoPrimes M, ∀ P : Subgroup G, Prep03.IsSylowTop p P →
      IsMulCommutative ↥P
  ·
    have hsetup' : Prep03.IsSigmaComplementSetup G M E K U :=
      ⟨hGamb, hsetup.isCoatom, hdecomp, le_sup_right, hKhall, le_sup_left, hdecompE⟩
    obtain ⟨U₁, U₀, hU₁U, hU₀U, hU₁ab, hUnorm, hinertia, hexp, hfree⟩ :=
      FNI_abelian_ambient_normal_hall_inertia_and_exponent h₁ h₂ h₄ h₅ h₆ h₈ G hGamb M E K U
        hsetup' hU hab
    refine ⟨U₁, U₀, hU₁U, hU₀U, hU₁ab,
      (normal_subgroupOf_iff_le_normalizer hU₁U).2 hUnorm, ?_, hexp, ?_⟩
    · intro h hh hh1
      rw [heq] at hh
      exact hinertia h hh hh1
    · intro x hx hx1
      rw [heq]
      exact hfree x hx hx1
  ·
    push Not at hab
    obtain ⟨p, hp, P, hP, hPab⟩ := hab
    obtain ⟨A, hAE, hAplane⟩ :=
      _root_.CFSG.FeitThompson.Proofs.exists_plane_le_of_isInternalSemidirectProduct hp
        hsetup.semidirect_M
    have hplane : Prep03.IsPlaneSetup G p M A E :=
      ⟨hGamb, hsetup.isCoatom, prime_of_mem_tauTwoPrimes hp,
        notMem_sigmaPrimes_of_mem_tauTwoPrimes hp, hAE.trans hEM,
        _root_.CFSG.FeitThompson.Proofs.isPlane_of_isElementaryAbelianPlane hAplane, hdecomp, hAE⟩
    set A₀ : Subgroup G := Prep03.cent A ((sigmaCore M : Subgroup G) : Set G) with hA₀def
    obtain ⟨hA₀U, hA₀ab, hUnorm, V, hVsemi, -, hexp, hVfree, hinertia⟩ :=
      FNI_nonabelian_ambient_normal_hall_free_complement h₁ h₃ h₅ G hGamb p M A E K U hplane
        ⟨P, hP, hPab⟩ hKhall le_sup_right le_sup_left hdecompE A₀ hA₀def
    refine ⟨A₀, V, hA₀U, hVsemi.2.1, hA₀ab,
      (normal_subgroupOf_iff_le_normalizer hA₀U).2 hUnorm, ?_, hexp, ?_⟩
    · intro h hh hh1
      rw [heq] at hh
      exact le_of_eq (hinertia h hh hh1)
    · intro x hx hx1
      rw [heq]
      exact hVfree x hx hx1

end

end CFSG.FeitThompson.Proofs
