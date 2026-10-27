module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
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
open CFSG.FeitThompson.Prep08 Subgroup

universe u

variable {G : Type u} [Group G]

theorem exists_sigmaComplement [Finite G] (hna : ¬ IsMulCommutative G) [Nontrivial G]
    {M : Subgroup G} (hM : IsCoatom M) (hsolv : Group.IsSolvable ↥M)
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hder : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    ∃ E : Subgroup G, E ≤ M ∧ E ≠ ⊥ ∧
      FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E := by
  have := hsolv
  set s : Subgroup ↥M := (sigmaCore M).subgroupOf M with hs
  have hsmap : s.map M.subtype = sigmaCore M := Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)
  have hsHall : IsHallPiSubgroup (sigmaPrimes M) s := hHall.2
  obtain ⟨T, hT⟩ := exists_isHallSubgroup (X := ↥M) ((sigmaPrimes M)ᶜ)
  have hscard : IsPiNumber (sigmaPrimes M) (Nat.card ↥s) :=
    isPiSubgroup_iff_isPiNumber.1 hsHall.isPiSubgroup
  have hsindex : IsPiNumber ((sigmaPrimes M)ᶜ) s.index :=
    isPiNumber_iff.2 fun p hp => hsHall.notMem_of_mem_primeFactors_index p hp
  have hcop1 : (Nat.card ↥s).Coprime (Nat.card ↥T) :=
    hscard.coprime_of_compl hT.natCard Nat.card_pos.ne' Nat.card_pos.ne'
  have hcop2 : s.index.Coprime T.index :=
    hsindex.coprime_of_compl hT.index Subgroup.index_ne_zero_of_finite
      Subgroup.index_ne_zero_of_finite
  have hprod : Nat.card ↥T * T.index = Nat.card ↥s * s.index := by
    rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
  have hTdvd : Nat.card ↥T ∣ s.index :=
    hcop1.symm.dvd_of_dvd_mul_left ⟨T.index, hprod.symm⟩
  have hidvd : s.index ∣ Nat.card ↥T :=
    hcop2.dvd_of_dvd_mul_right ⟨Nat.card ↥s, by rw [hprod, Nat.mul_comm]⟩
  have hTeq : Nat.card ↥T = s.index := Nat.dvd_antisymm hTdvd hidvd
  have hcardprod : Nat.card ↥s * Nat.card ↥T = Nat.card ↥M := by
    rw [hTeq]; exact Subgroup.card_mul_index s
  have hdisj : Disjoint s T := Subgroup.disjoint_of_coprime_natCard hcop1
  have hsup : s ⊔ T = ⊤ :=
    (Subgroup.isComplement'_of_card_mul_and_disjoint hcardprod hdisj).sup_eq_top
  refine ⟨T.map M.subtype, Subgroup.map_subtype_le _, ?_, ?_, le_normalizer_sigmaCore M, ?_⟩
  ·
    intro hbot
    have hT1 : Nat.card ↥T = 1 := by
      rw [← Subgroup.card_map_of_injective (K := T) M.subtype_injective, hbot, Subgroup.card_bot]
    have hstop : s = ⊤ := Subgroup.index_eq_one.1 (hTeq.symm.trans hT1)
    have hSM : sigmaCore M = M := by
      rw [← hsmap, hstop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact ne_bot_of_isCoatom hna hM
      (eq_bot_of_isSolvable_of_le_commutator_self M (hSM.symm.le.trans hder))
  · calc sigmaCore M ⊔ T.map M.subtype = (s ⊔ T).map M.subtype := by
          rw [Subgroup.map_sup, hsmap]
      _ = M := by rw [hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [disjoint_iff, ← hsmap, ← Subgroup.map_inf _ _ _ M.subtype_injective,
      disjoint_iff.1 hdisj, Subgroup.map_bot]

theorem isHallOf_and_coprime_of_isInternalSemidirectProduct [Finite G] {M E : Subgroup G}
    (hHall : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M)
    (hEM : E ≤ M) (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E) :
    IsHallOf {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} E M ∧
      (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E) := by
  have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hsd.natCard_eq_mul
  set s : Subgroup ↥M := (sigmaCore M).subgroupOf M with hs
  set e : Subgroup ↥M := E.subgroupOf M with he
  have hscard : Nat.card ↥s = Nat.card ↥(sigmaCore M) := natCard_subgroupOf (sigmaCore_le M)
  have hecard : Nat.card ↥e = Nat.card ↥E := natCard_subgroupOf hEM
  have hsidx : s.index = Nat.card ↥E := by
    have h := Subgroup.card_mul_index s
    rw [hscard, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have heidx : e.index = Nat.card ↥(sigmaCore M) := by
    have h := Subgroup.card_mul_index e
    rw [hecard, hcard, Nat.mul_comm (Nat.card ↥(sigmaCore M))] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hEpi : IsPiNumber ((sigmaPrimes M)ᶜ) (Nat.card ↥E) := by
    rw [← hsidx]
    exact isPiNumber_iff.2 fun p hp => hHall.2.notMem_of_mem_primeFactors_index p hp
  refine ⟨⟨hEM, ⟨isPiSubgroup_iff.2 fun p hp => ?_, fun p hp hp' => ?_⟩⟩, ?_⟩
  · rw [hecard] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, isPiNumber_iff.1 hEpi p hp⟩
  · rw [heidx] at hp
    exact hp'.2 (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p hp)
  · exact (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sigmaCore M)).coprime_of_compl hEpi
      Nat.card_pos.ne' Nat.card_pos.ne'

theorem FTS_sigma_complement_exists_nontrivial
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_sigma_complement_exists_nontrivial.{u} := by
  intro G _ _ hG M hM
  have : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup.toNontrivial
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hHall, -, hder⟩ := h₁ G hG2 M hM
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  exact ⟨exists_sigmaComplement hG.not_isMulCommutative hM hsolv hHall hder,
    fun E hEM hsd => isHallOf_and_coprime_of_isInternalSemidirectProduct hHall hEM hsd⟩

end

end CFSG.FeitThompson.Proofs
