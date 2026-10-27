module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaNontrivialComplementStructure
import CFSG.FeitThompson.Local.NonTIFittingNilpotentCoreBetaExclusion
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Foundations.HallCoreOfNormalHallOvergroup
import CFSG.FeitThompson.Local.FittingSharpTISetNormalizer
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Representations.TINormalCentralSectionGeometry
import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
import CFSG.FeitThompson.Definitions.NormalSylowHallCore
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup _root_.CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem hallCoreIn_eq_of_normal_hall [Finite G] {M N : Subgroup G} (hNM : N ≤ M)
    (hnorm : (N.subgroupOf M).Normal) (hcop : (Nat.card ↥N).Coprime (N.relIndex M))
    (hle : hallCoreIn M ≤ N) : hallCoreIn N = hallCoreIn M := by
  have hcard : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcop' : (Nat.card ↥(N.subgroupOf M)).Coprime (N.subgroupOf M).index := by
    rw [hcard]; exact hcop
  have hle' : hallCore ↥M ≤ N.subgroupOf M := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, ← hallCoreIn_eq]
    exact hle
  have key := map_subtype_hallCore_eq_hallCore hnorm hcop' hle'
  have hmap : (hallCore ↥(N.subgroupOf M)).map
      (Subgroup.subgroupOfEquivOfLe hNM : ↥(N.subgroupOf M) →* ↥N) = hallCore ↥N :=
    map_hallCore (Subgroup.subgroupOfEquivOfLe hNM)
  rw [hallCoreIn_eq, hallCoreIn_eq, ← key, ← hmap, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem kappaPrimes_nonempty_of_hall_ne_bot [Finite G] {M K : Subgroup G}
    (hK : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M)) (hKle : K ≤ M) (hKbot : K ≠ ⊥) :
    (kappaPrimes M).Nonempty := by
  have hcard : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hlt : 1 < Nat.card ↥K :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hKbot (Subgroup.card_eq_one.1 h))
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.2 hlt
  exact ⟨r, (isHallPiSubgroup_iff.1 hK).1 r (by rw [hcard]; exact hr)⟩

theorem sigmaPrimes_nonempty_of_sigmaCore_ne_bot [Finite G] {M : Subgroup G}
    (hS : sigmaCore M ≠ ⊥) : (sigmaPrimes M).Nonempty := by
  have hlt : 1 < Nat.card ↥(sigmaCore M) :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hS (Subgroup.card_eq_one.1 h))
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.2 hlt
  exact ⟨r, isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r hr⟩

theorem coprime_natCard_relIndex_commutator [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsHallPiSubgroup (kappaPrimes M) (K.subgroupOf M))
    (hcard : Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K) :
    (Nat.card ↥(⁅M, M⁆ : Subgroup G)).Coprime ((⁅M, M⁆ : Subgroup G).relIndex M) := by
  have hKcard : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hMle : (⁅M, M⁆ : Subgroup G) ≤ M := Subgroup.commutator_le_self M
  have hidx : (⁅M, M⁆ : Subgroup G).relIndex M = Nat.card ↥K := by
    have h := natCard_mul_relIndex hMle
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hidxK : (K.subgroupOf M).index = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    have h : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      have := natCard_mul_relIndex hKM
      simpa [Subgroup.relIndex] using this
    rw [hcard, mul_comm (Nat.card ↥(⁅M, M⁆ : Subgroup G))] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  obtain ⟨hKπ, hKπ'⟩ := isHallPiSubgroup_iff.1 hK
  rw [hidx]
  by_contra hc
  obtain ⟨p, hp, hpM', hpK⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  have h1 : p ∈ kappaPrimes M :=
    hKπ p (Nat.mem_primeFactors.2 ⟨hp, by rw [hKcard]; exact hpK, Nat.card_pos.ne'⟩)
  have h2 : p ∉ kappaPrimes M :=
    hKπ' p (Nat.mem_primeFactors.2 ⟨hp, by rw [hidxK]; exact hpM', Nat.card_pos.ne'⟩)
  exact h2 h1

theorem isFittingOverlapSetup_of_mem_inter_conjSet [Finite G] {M : Subgroup G} (hM : IsCoatom M)
    {g x : G} (hgM : g ∉ M)
    (hx : x ∈ sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g) :
    IsFittingOverlapSetup M (mixedFitting M ⊓ conjSubgroup (mixedFitting M) g) g := by
  obtain ⟨⟨hxF, hx1⟩, y, ⟨hyF, -⟩, hxy⟩ := hx
  refine ⟨hM, hgM, rfl, fun hbot => hx1 ?_⟩
  have hmem : x ∈ mixedFitting M ⊓ conjSubgroup (mixedFitting M) g :=
    ⟨hxF, mem_conjSubgroup.2 ⟨y, hyF, hxy⟩⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson Subgroup
open _root_.CFSG.FeitThompson

universe u

theorem FBG_local_p_nontrivial_U_case
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_local_p_nontrivial_U_case.{u} := by
  intro G _ _ hG M K U hsetup hKbot hUbot
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hM := hsetup.isCoatom
  have hκ : (kappaPrimes M).Nonempty :=
    kappaPrimes_nonempty_of_hall_ne_bot hsetup.hall_K hsetup.le_M_K hKbot
  have hres : IsKappaResidualSetup M K U :=
    { isCoatom := hM
      kappaPrimes_nonempty := hκ
      le_M_K := hsetup.le_M_K
      hall_K := hsetup.hall_K
      le_M_U := hsetup.le_M_U
      ne_bot_U := hUbot
      semidirect_M := hsetup.semidirect_M
      semidirect_UK := hsetup.semidirect_UK }
  obtain ⟨hKprime, hbeta, hnil, -, -⟩ :=
    FBG_kappa_nontrivial_complement_structure h₃ h₅ h₆ h₇ h₈ G hG M K U hres
  obtain ⟨Y, hY⟩ :=
    CFSG.FeitThompson.exists_isSylowProduct (mixedFitting M)
      {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M}
  obtain ⟨hHS, hSbot, -, -, hdirect, -, hHle, -, -⟩ := h₁ G hG M hM hnil Y hY
  have hSF : sigmaCore M ≤ mixedFitting M := hdirect.left_le
  have hFbot : mixedFitting M ≠ ⊥ := fun h => hSbot (le_bot_iff.1 (h ▸ hSF))
  have hnormF : normalizer (sharp (mixedFitting M)) = M := by
    rw [sharp_eq, normalizer_sdiff_singleton_one]
    exact normalizer_eq_of_isCoatom hM hFbot (mixedFitting_le M) (le_normalizer_mixedFitting M)
  have hσne : (sigmaPrimes M).Nonempty := sigmaPrimes_nonempty_of_sigmaCore_ne_bot hSbot
  have hdisj : ∀ g : G, g ∉ M →
      sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g = ∅ := by
    intro g hgM
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hX := isFittingOverlapSetup_of_mem_inter_conjSet hM hgM hx
    obtain ⟨-, -, -, hβ, -⟩ :=
      FBG_nonti_fitting_nilpotent_core_and_beta_exclusion h₁ h₂ h₃ h₈ G hG M _ g hX Y hY
    obtain ⟨r, hr⟩ := hσne
    rw [hbeta, hβ] at hr
    exact hr
  have hTI : IsTIWithNormalizer (sharp (mixedFitting M)) M :=
    isTIWithNormalizer_sharp_mixedFitting hnormF hFbot hdisj
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hKhall3 : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallPiSubgroupOf ⟨hsetup.le_M_K, hsetup.hall_K⟩
  have hsetup3 : Prep03.IsKappaSetup G M K (Prep03.cent (sigmaCore M) (K : Set G))
      (K ⊔ Prep03.cent (sigmaCore M) (K : Set G)) :=
    ⟨hamb, hM, hκ, hKhall3, rfl, rfl⟩
  obtain ⟨hsemi, -, -⟩ := FNI_kappa_derived_complement h₄ h₅ G M K _ _ hsetup3
  have hcard : Nat.card ↥M = Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K :=
    CFSG.FeitThompson.natCard_of_isSemidirect hsemi
  have hHM : hallCoreIn (⁅M, M⁆ : Subgroup G) = hallCoreIn M :=
    hallCoreIn_eq_of_normal_hall (Subgroup.commutator_le_self M)
      (normal_subgroupOf_commutator_self M)
      (coprime_natCard_relIndex_commutator hsetup.le_M_K hsetup.hall_K hcard) hHle
  exact ⟨hKprime, hTI, hHM, hHS⟩

end

end CFSG.FeitThompson.Proofs
