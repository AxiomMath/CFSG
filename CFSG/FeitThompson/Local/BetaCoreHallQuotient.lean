module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimeDerivedComplement
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.NormalComplementsPiCoreQuotient
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.InvariantHallPiSubgroupExtension
import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
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

universe u

variable {G : Type u} [Group G] {M : Subgroup G}

theorem le_normalizer_commutator_self (M : Subgroup G) :
    M ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self M)).1
    (normal_subgroupOf_commutator_self M)

variable [Finite G]

instance betaCore_characteristic_subgroupOf (M : Subgroup G) :
    ((betaCore M).subgroupOf M).Characteristic := by
  rw [subgroupOf_betaCore]; exact piCore_characteristic _ _

theorem betaCore_le_commutator (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) : betaCore M ≤ (⁅M, M⁆ : Subgroup G) := by
  have := hG.simple
  exact (le_sigmaCore (betaCore_le M) (betaCore_normal_subgroupOf M)
    ((isPiSubgroup_betaCore M).mono
      (betaPrimes_subset_sigmaPrimes hG.nonabelian hG.odd hG.solvable hM))).trans hSM

theorem betaCore_eq_map_piCore_commutator (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    betaCore M =
      (piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype := by
  have hBM' : betaCore M ≤ (⁅M, M⁆ : Subgroup G) := betaCore_le_commutator hG hM hSM
  refine le_antisymm ?_ ?_
  · rw [le_map_piCore_iff _ hBM']
    refine le_piCore (normal_subgroupOf_of_le_normalizer hBM'
      ((Subgroup.commutator_le_self M).trans (le_normalizer_betaCore M))) ?_
    refine isPiSubgroup_map_subtype_iff.1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hBM']
    exact isPiSubgroup_betaCore M
  · have hDle : (piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G)).map
        (⁅M, M⁆ : Subgroup G).subtype ≤ (⁅M, M⁆ : Subgroup G) := Subgroup.map_subtype_le _
    refine le_betaCore (hDle.trans (Subgroup.commutator_le_self M))
      (normal_subgroupOf_of_le_normalizer (hDle.trans (Subgroup.commutator_le_self M))
        ((le_normalizer_commutator_self M).trans
          (normalizer_le_normalizer_map_subtype _ _))) ?_
    exact isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_piCore _ _)

theorem subgroupOf_betaCore_commutator (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    (betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G) =
      piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G) := by
  rw [betaCore_eq_map_piCore_commutator hG hM hSM, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective (⁅M, M⁆ : Subgroup G).subtype_injective]

theorem normal_subgroupOf_betaCore_commutator (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    ((betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal := by
  rw [subgroupOf_betaCore_commutator hG hM hSM]; exact piCore_normal _ _

theorem notMem_betaPrimes_of_dvd_relIndex_commutator_self
    (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) {p : ℕ}
    (hdvd : p ∣ (⁅M, M⁆ : Subgroup G).relIndex M) : p ∉ betaPrimes ↥M := by
  have := hG.simple
  intro hp
  have hpσ : p ∈ sigmaPrimes M :=
    betaPrimes_subset_sigmaPrimes hG.nonabelian hG.odd hG.solvable hM hp
  have hmul := Subgroup.relIndex_mul_relIndex (sigmaCore M) (⁅M, M⁆ : Subgroup G) M hSM
    (Subgroup.commutator_le_self M)
  refine hHall.notMem_of_mem_primeFactors_index (p := p) ?_ hpσ
  rw [index_subgroupOf]
  refine Nat.mem_primeFactors.2 ⟨prime_of_mem_sigmaPrimes hpσ, hmul ▸ hdvd.mul_left _, ?_⟩
  rw [← index_subgroupOf]
  exact Subgroup.index_ne_zero_of_finite

section Hyp

variable (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u})
  (hG : Prep06.IsMinimalOddSimple G) (hM : IsCoatom M)

include h₂ hG hM in
theorem exists_index_pComplCore_commutator_eq_pow
    {p : ℕ} (hp : p ∈ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).primeFactors)
    (hbeta : p ∉ betaPrimes ↥M) :
    ∃ a : ℕ, (pComplCore p ↥(⁅M, M⁆ : Subgroup G)).index = p ^ a := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hodd : Odd p := hG.odd.of_dvd_nat
    ((Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_subgroup_dvd_card _))
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩
  obtain ⟨n, hn⟩ := exists_relIndex_derived_eq_pow h₂ hG8 hM hpp hodd hbeta
  exact ⟨n, by rwa [relIndex_prep06_pComplCoreIn] at hn⟩

include h₂ hG hM in
theorem isHallPiSubgroup_piCore_commutator :
    IsHallPiSubgroup (betaPrimes ↥M) (piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G)) := by
  have hsolv : Group.IsSolvable ↥(⁅M, M⁆ : Subgroup G) :=
    isSolvable_of_le_of_isSolvable (Subgroup.commutator_le_self M) (hG.solvable M hM.1)
  exact isHallPiSubgroup_piCore fun _ hp hpb =>
    exists_index_pComplCore_commutator_eq_pow h₂ hG hM hp hpb

include h₂ hG hM in
theorem isNilpotent_quotient_piCore_commutator :
    Group.IsNilpotent (↥(⁅M, M⁆ : Subgroup G) ⧸ piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G)) :=
  isNilpotent_quotient_piCore fun _ hp hpb =>
    exists_index_pComplCore_commutator_eq_pow h₂ hG hM hp hpb

include h₂ hG hM in
theorem notMem_betaPrimes_of_dvd_relIndex_betaCore_commutator
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) {p : ℕ}
    (hdvd : p ∣ (betaCore M).relIndex (⁅M, M⁆ : Subgroup G)) : p ∉ betaPrimes ↥M := by
  intro hp
  have hrel : (betaCore M).relIndex (⁅M, M⁆ : Subgroup G) =
      (piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G)).index := by
    rw [← index_subgroupOf, subgroupOf_betaCore_commutator hG hM hSM]
  refine (isHallPiSubgroup_piCore_commutator h₂ hG hM).notMem_of_mem_primeFactors_index
    (p := p) ?_ hp
  exact Nat.mem_primeFactors.2 ⟨prime_of_mem_betaPrimes hp, hrel ▸ hdvd,
    hrel ▸ Subgroup.index_ne_zero_of_finite⟩

include h₂ hG hM in
theorem isHallPiIn_betaCore
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    Prep06.IsHallPiIn (betaPrimes ↥M) (betaCore M) M := by
  refine ⟨betaCore_le M, fun p hp => isPiSubgroup_iff.1 (isPiSubgroup_betaCore M) p hp,
    fun p hp => ?_⟩
  have hBM' : betaCore M ≤ (⁅M, M⁆ : Subgroup G) := betaCore_le_commutator hG hM hSM
  have hmul := Subgroup.relIndex_mul_relIndex (betaCore M) (⁅M, M⁆ : Subgroup G) M hBM'
    (Subgroup.commutator_le_self M)
  have hdvd : p ∣ (betaCore M).relIndex (⁅M, M⁆ : Subgroup G) *
      (⁅M, M⁆ : Subgroup G).relIndex M := hmul ▸ Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul (Nat.prime_of_mem_primeFactors hp)).1 hdvd with h | h
  · exact notMem_betaPrimes_of_dvd_relIndex_betaCore_commutator h₂ hG hM hSM h
  · exact notMem_betaPrimes_of_dvd_relIndex_commutator_self hG hM hHall hSM h

include h₂ hG hM in
theorem isHallPiIn_betaCore_top
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    Prep06.IsHallPiIn (betaPrimes ↥M) (betaCore M) ⊤ := by
  have := hG.simple
  refine ⟨le_top, fun p hp => isPiSubgroup_iff.1 (isPiSubgroup_betaCore M) p hp, fun p hp => ?_⟩
  rw [Subgroup.relIndex_top_right] at hp
  have hmul := Subgroup.relIndex_mul_index (betaCore_le M)
  have hdvd : p ∣ (betaCore M).relIndex M * M.index := hmul ▸ Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul (Nat.prime_of_mem_primeFactors hp)).1 hdvd with h | h
  · exact (isHallPiIn_betaCore h₂ hG hM hHall hSM).2.2 p
      (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp, h,
        Subgroup.index_ne_zero_of_finite (H := (betaCore M).subgroupOf M)⟩)
  · intro hpβ
    exact not_dvd_index_of_mem_sigmaPrimes
      (betaPrimes_subset_sigmaPrimes hG.nonabelian hG.odd hG.solvable hM hpβ) h

end Hyp

theorem FTS_beta_core_hall_quotient
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_beta_core_hall_quotient.{u} := by
  intro G _ _ hG M hM
  have hMc : IsCoatom M := hM
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨hHallM, -, hSM⟩ := h₁ G hG2 M hMc
  have hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) := hHallM.2
  have heq : (betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G) =
      piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G) :=
    subgroupOf_betaCore_commutator hG hMc hSM
  refine ⟨betaCore_characteristic_subgroupOf M, le_normalizer_betaCore M,
    isHallPiIn_betaCore h₂ hG hMc hHall hSM, betaCore_le_commutator hG hMc hSM,
    isHallPiIn_betaCore_top h₂ hG hMc hHall hSM,
    normal_subgroupOf_betaCore_commutator hG hMc hSM, ?_⟩
  have hN : ((betaCore M).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
    normal_subgroupOf_betaCore_commutator hG hMc hSM
  exact Group.nilpotent_of_mulEquiv (_h := isNilpotent_quotient_piCore_commutator h₂ hG hMc)
    (QuotientGroup.quotientMulEquivOfEq heq.symm)

end

end CFSG.FeitThompson.Proofs
