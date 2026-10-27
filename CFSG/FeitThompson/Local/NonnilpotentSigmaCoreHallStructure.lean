module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.ResidualComplementNilpotentCore
import CFSG.FeitThompson.Local.ExceptionalPrimeFixedConfiguration
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.KappaResidualInPrescribedComplement
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Foundations.SolvableHallExistence
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

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
open Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem kappaPrimes_nonempty
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsFBGAmbient G) {M : Subgroup G} (hM : IsCoatom M)
    (hSnotnil : ¬ Group.IsNilpotent ↥(sigmaCore M)) : (kappaPrimes M).Nonempty := by
  have _i : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallOf, -, hSle⟩ := h₁ G hG02 M hM
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have hSlt : sigmaCore M < M := by
    refine lt_of_le_of_ne hSM ?_
    intro heq
    have : Group.IsSolvable ↥M := hG.isSolvable M hM.1
    rw [heq] at hSle
    have hMbot : M = ⊥ := eq_bot_of_isSolvable_of_le_commutator_self M hSle
    exact hSnotnil (by rw [heq, hMbot]; infer_instance)
  have hidxne : ((sigmaCore M).subgroupOf M).index ≠ 1 := fun h =>
    absurd (Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h)) hSlt.not_ge
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hidxne
  have _fp := Fact.mk hp
  have hpσ : p ∉ sigmaPrimes M := hHallOf.2.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨hp, hpdvd, Subgroup.index_ne_zero_of_finite⟩)
  have hpM : p ∣ Nat.card ↥M := hpdvd.trans (Subgroup.index_dvd_card _)
  obtain ⟨S₀⟩ : Nonempty (Sylow p ↥M) := inferInstance
  by_contra hempty
  have hpκ : p ∉ kappaPrimes M := fun h => hempty ⟨p, h⟩
  have hGmin : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨-, -, hnil⟩ := FNI_outside_sigma_kappa_sylow_core_nilpotent h₁ h₄ h₅ G hGmin p M
    ((S₀ : Subgroup ↥M).map M.subtype) hM hp hpM
    (by rintro (h | h); exacts [hpσ h, hpκ h]) ⟨S₀, rfl⟩
  exact hSnotnil hnil

theorem hallPiSubgroupOf_kappaPrimes_exists {M : Subgroup G} (hMsolv : Group.IsSolvable ↥M) :
    ∃ K : Subgroup G, IsHallPiSubgroupOf (kappaPrimes M) K M := by
  have := hMsolv
  obtain ⟨K₀, hK₀⟩ := exists_isHallSubgroup (X := ↥M) (kappaPrimes M)
  refine ⟨K₀.map M.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact isHallSubgroup_iff_isHallPiSubgroup.1 hK₀

theorem isInternalSemidirectProduct_sigmaCore
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsFBGAmbient G) {M K : Subgroup G} (hM : IsCoatom M)
    (hSnotnil : ¬ Group.IsNilpotent ↥(sigmaCore M)) (hκ : (kappaPrimes M).Nonempty)
    (hK : IsHallPiSubgroupOf (kappaPrimes M) K M) :
    Prep03.IsSemidirect M (sigmaCore M) K ∧ K ≠ ⊥ := by
  have _i : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hamb03 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    CFSG.FeitThompson.isHallPiOf_of_isHallPiSubgroupOf hK
  obtain ⟨hKbot, U, E₁, -, -, hsemiM, hsemiUK, -⟩ := h₂ G hamb03 M K hM hκ hKH
  have hUM : U ≤ M := le_sup_left.trans hsemiM.2.1
  have hHne : hallCoreIn M ≠ sigmaCore M := fun h =>
    hSnotnil ((FBG_normal_hall_core_sigma_containment.{u} G hG M hM).2.1 h)
  have hU : U = ⊥ :=
    (FBG_residual_complement_nilpotent_core h₁ h₄ h₅ G hG02 M hM K U hK hUM
      (CFSG.FeitThompson.isInternalSemidirectProduct_of_isSemidirect hsemiM)
      (CFSG.FeitThompson.isInternalSemidirectProduct_of_isSemidirect
        hsemiUK)).2 hHne
  refine ⟨?_, hKbot⟩
  have h := hsemiM
  rwa [hU, bot_sup_eq] at h

theorem natCard_prime_of_isHallPiSubgroupOf_kappaPrimes
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsFBGAmbient G) {M K : Subgroup G} (hM : IsCoatom M)
    (hSnotnil : ¬ Group.IsNilpotent ↥(sigmaCore M)) (hκ : (kappaPrimes M).Nonempty)
    (hK : IsHallPiSubgroupOf (kappaPrimes M) K M) :
    FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K ∧ (Nat.card ↥K).Prime ∧
      (Nat.card ↥(centralizerWithin (sigmaCore M) K)).Prime := by
  have _i : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hamb03 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    CFSG.FeitThompson.isHallPiOf_of_isHallPiSubgroupOf hK
  obtain ⟨hsd, hKbot⟩ :=
    isInternalSemidirectProduct_sigmaCore h₁ h₂ h₄ h₅ hG hM hSnotnil hκ hK
  have hsdFC : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K :=
    CFSG.FeitThompson.isInternalSemidirectProduct_of_isSemidirect hsd
  have hAeq : Prep03.cent (sigmaCore M) (K : Set G) = centralizerWithin (sigmaCore M) K := rfl
  have hsetup : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) :=
    { ambient := hamb03
      isCoatom := hM
      kappa_nonempty := hκ
      isHall_K := hKH
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨-, -, hAprime, hAall⟩ := h₃ G M K _ _ hsetup hsd
  have hcent : ∀ k ∈ K, k ≠ 1 →
      sigmaCore M ⊓ centralizer ({k} : Set G) = Prep03.cent (sigmaCore M) (K : Set G) := by
    intro k hk hk1
    have hXK : zpowers k ≤ K := zpowers_le.2 hk
    have hXbot : zpowers k ≠ ⊥ := fun h => hk1 (Subgroup.mem_bot.1 (h ▸ mem_zpowers k))
    have hcz : centralizer ({k} : Set G) = centralizer ((zpowers k : Subgroup G) : Set G) := by
      rw [zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcz]
    exact hAall (zpowers k) hXK hXbot
  obtain ⟨hKprime, -⟩ :=
    FBG_prime_fixed_exceptional_hall_core h₁ G hG02 M hM K hKbot hK.1 hsdFC hSnotnil _ hAprime
      (Prep03.cent (sigmaCore M) (K : Set G)) rfl rfl hcent (hallCoreIn M) rfl
  exact ⟨hsdFC, hKprime, hAeq ▸ hAprime⟩

theorem hallCore_and_fitting_structure
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u})
    (hG : IsFBGAmbient G) {M : Subgroup G} (hM : IsCoatom M)
    (hSnotnil : ¬ Group.IsNilpotent ↥(sigmaCore M)) (hκ : (kappaPrimes M).Nonempty) :
    ⊥ < hallCoreIn M ∧ hallCoreIn M < sigmaCore M ∧ sigmaCore M = ⁅M, M⁆ ∧
      IsNilpotentQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M ∧
      ((mixedFitting M : Set G) = (hallCoreIn M : Set G) *
        ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G)) ∧
      mixedFitting M < ⁅M, M⁆ ∧
      normalizer (sharp (mixedFitting M)) = M ∧
      ∀ g : G, g ∉ M → sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅ := by
  have _i : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hamb03 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable M hM.1
  obtain ⟨K, hK⟩ := hallPiSubgroupOf_kappaPrimes_exists hMsolv
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    CFSG.FeitThompson.isHallPiOf_of_isHallPiSubgroupOf hK
  obtain ⟨hsd, hKbot⟩ :=
    isInternalSemidirectProduct_sigmaCore h₁ h₂ h₄ h₅ hG hM hSnotnil hκ hK
  have hsdFC : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K :=
    CFSG.FeitThompson.isInternalSemidirectProduct_of_isSemidirect hsd
  have hsetup : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) :=
    { ambient := hamb03
      isCoatom := hM
      kappa_nonempty := hκ
      isHall_K := hKH
      A_eq := rfl
      Z_eq := rfl }
  obtain ⟨-, -, hAprime, hAall⟩ := h₃ G M K _ _ hsetup hsd
  have hcent : ∀ k ∈ K, k ≠ 1 →
      sigmaCore M ⊓ centralizer ({k} : Set G) = Prep03.cent (sigmaCore M) (K : Set G) := by
    intro k hk hk1
    have hXK : zpowers k ≤ K := zpowers_le.2 hk
    have hXbot : zpowers k ≠ ⊥ := fun h => hk1 (Subgroup.mem_bot.1 (h ▸ mem_zpowers k))
    have hcz : centralizer ({k} : Set G) = centralizer ((zpowers k : Subgroup G) : Set G) := by
      rw [zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcz]
    exact hAall (zpowers k) hXK hXbot
  obtain ⟨-, hHbot, hHS, hSeq, hnilq, hcomm, hFeq, hFlt, hnorm, hTI⟩ :=
    FBG_prime_fixed_exceptional_hall_core h₁ G hG02 M hM K hKbot hK.1 hsdFC hSnotnil _ hAprime
      (Prep03.cent (sigmaCore M) (K : Set G)) rfl rfl hcent (hallCoreIn M) rfl
  have hFcoe : CFSG.FeitThompson.fittingIn M = mixedFitting M := by
    rw [mixedFitting_eq]; rfl
  have hsharp : fittingRawSharp M = sharp (mixedFitting M) := by
    rw [fittingRawSharp_eq, mixedFitting_eq]; rfl
  have hHne : hallCoreIn M ≠ sigmaCore M := fun h =>
    hSnotnil ((FBG_normal_hall_core_sigma_containment.{u} G hG M hM).2.1 h)
  rw [hFcoe] at hcomm hFeq hFlt
  refine ⟨bot_lt_iff_ne_bot.2 hHbot, lt_of_le_of_ne hHS hHne, hSeq, hnilq, hcomm, hFeq, hFlt, ?_,
    fun g hg => ?_⟩
  · rw [← hsharp]; exact hnorm
  · rw [← hsharp]; exact hTI g hg

theorem FBG_nonnilpotent_sigma_core_hall_structure
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₄ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u} := by
  intro G _ _ hG M hM hSnotnil
  have hκ : (kappaPrimes M).Nonempty := kappaPrimes_nonempty h₁ h₄ h₅ hG hM hSnotnil
  obtain ⟨h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    hallCore_and_fitting_structure h₁ h₂ h₃ h₄ h₅ hG hM hSnotnil hκ
  exact ⟨hκ, fun K hKM hKhall => natCard_prime_of_isHallPiSubgroupOf_kappaPrimes h₁ h₂ h₃ h₄ h₅ hG
    hM hSnotnil hκ ⟨hKM, hKhall⟩, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end

end CFSG.FeitThompson.Proofs
