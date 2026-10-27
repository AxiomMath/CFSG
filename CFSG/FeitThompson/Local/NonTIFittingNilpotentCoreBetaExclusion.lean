module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X Y : Subgroup G} {g : G} {p : ℕ}

theorem isNilpotent_sigmaCore_of_isFittingOverlapSetup
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g) :
    Group.IsNilpotent ↥(sigmaCore M) := by
  by_contra hnil
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTI⟩ := h₂ G hG M hsetup.isCoatom hnil
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hsetup.ne_bot
  have hx1' : x ≠ 1 := by simpa using hx1
  rw [hsetup.eq] at hxX
  obtain ⟨hxF, hxc⟩ := hxX
  obtain ⟨y, hyF, hyx⟩ := mem_conjSubgroup.1 hxc
  have hy1 : y ≠ 1 := by
    intro h
    rw [h] at hyx
    simp only [mul_one, inv_mul_cancel] at hyx
    exact hx1' hyx.symm
  have hmem : x ∈ sharp (mixedFitting M) ∩ conjSet (sharp (mixedFitting M)) g :=
    ⟨⟨hxF, hx1'⟩, ⟨y, ⟨hyF, hy1⟩, hyx⟩⟩
  rw [hTI g hsetup.notMem] at hmem
  exact hmem

theorem isCyclic_map_pCore_of_notMem_sigmaPrimes (hp : p.Prime) (hpσ : p ∉ sigmaPrimes M)
    (hprod : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y) (hYcyc : IsCyclic ↥Y) :
    IsCyclic ↥((pCore p ↥M).map M.subtype) := by
  have := Fact.mk hp
  have hOpF : (pCore p ↥M).map M.subtype ≤ mixedFitting M := by
    rw [mixedFitting_eq]
    exact Subgroup.map_mono
      (le_fittingRaw_of_isPGroup hp (pCore_normal p ↥M) (isPGroup_pCore hp ↥M))
  have hOpP : IsPGroup p ↥((pCore p ↥M).map M.subtype) :=
    (isPGroup_pCore hp ↥M).of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hpσ (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
  have hfac : (Nat.card ↥(mixedFitting M)).factorization p = (Nat.card ↥Y).factorization p := by
    rw [hprod.card_eq_mul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpS]
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥Y) := inferInstance
  have hQcard : Nat.card ↥((Q : Subgroup ↥Y).map Y.subtype)
      = p ^ (Nat.card ↥(mixedFitting M)).factorization p := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, Q.card_eq_multiplicity, hfac]
  have hQY : (Q : Subgroup ↥Y).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
  have hle : (pCore p ↥M).map M.subtype ≤ (Q : Subgroup ↥Y).map Y.subtype :=
    le_of_isPGroup_le_nilpotent (H := mixedFitting M)
      (mixedFitting_eq M ▸ isNilpotent_map_fittingRaw M) (hQY.trans hprod.right_le) hQcard
      hOpF hOpP
  exact isCyclic_of_le_of_isCyclic (hle.trans hQY) hYcyc

theorem mem_sigmaPrimes_of_mem_primeFactors_of_isFittingOverlapSetup (hG : IsFBGAmbient G)
    (hsetup : IsFittingOverlapSetup M X g)
    (hprod : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y) (hYcyc : IsCyclic ↥Y)
    (hp : p ∈ (Nat.card ↥X).primeFactors) : p ∈ sigmaPrimes M := by
  have := hG.isSimpleGroup
  by_contra hpσ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  refine not_isCyclic_map_pCore_of_dvd_natCard_inf_fittingRaw_conj hG.not_isMulCommutative
    hsetup.isCoatom hsetup.notMem hpp ?_
    (isCyclic_map_pCore_of_notMem_sigmaPrimes hpp hpσ hprod hYcyc)
  have hXeq : ((fittingRaw ↥M).map M.subtype ⊓
      ((fittingRaw ↥M).map M.subtype).map (MulAut.conj g⁻¹ : G →* G) : Subgroup G) = X := by
    rw [hsetup.eq, mixedFitting_eq, conjSubgroup_eq]
  rw [hXeq]
  exact Nat.dvd_of_mem_primeFactors hp

theorem le_sigmaCore_of_isFittingOverlapSetup (hG : IsFBGAmbient G)
    (hsetup : IsFittingOverlapSetup M X g)
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hprod : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y) (hYcyc : IsCyclic ↥Y) :
    X ≤ sigmaCore M := by
  have hXM : X ≤ M := hsetup.le.trans (mixedFitting_le M)
  have hpiX : IsPiSubgroup (sigmaPrimes M) (X.subgroupOf M) := by
    rw [isPiSubgroup_iff, natCard_subgroupOf_of_le' hXM]
    exact fun p hp =>
      mem_sigmaPrimes_of_mem_primeFactors_of_isFittingOverlapSetup hG hsetup hprod hYcyc hp
  have hle := Subgroup.map_mono (f := M.subtype) (hHall.le_of_isPiSubgroup hpiX)
  rwa [Subgroup.map_subgroupOf_eq_of_le hXM,
    Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at hle

theorem betaPrimes_eq_empty_of_isFittingOverlapSetup (hG : IsFBGAmbient G)
    (hsetup : IsFittingOverlapSetup M X g) (hSnil : Group.IsNilpotent ↥(sigmaCore M))
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hXS : X ≤ sigmaCore M) : betaPrimes ↥M = ∅ := by
  have := hG.isSimpleGroup
  have := hSnil
  have hXM : X ≤ M := hsetup.le.trans (mixedFitting_le M)
  refine Set.eq_empty_iff_forall_notMem.2 fun r hr => ?_
  have hrp : r.Prime := prime_of_mem_betaPrimes hr
  have := Fact.mk hrp
  have hrσ : r ∈ sigmaPrimes M := betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hsetup.isCoatom hr
  obtain ⟨Qr⟩ : Nonempty (Sylow r ↥(sigmaCore M)) := inferInstance
  have hQS : (Qr : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype ≤ sigmaCore M :=
    Subgroup.map_subtype_le _
  have hQM : (Qr : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype ≤ M :=
    hQS.trans (sigmaCore_le M)
  have hQcard : Nat.card ↥((Qr : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype)
      = r ^ (Nat.card ↥M).factorization r := by
    rw [Subgroup.card_map_of_injective (sigmaCore M).subtype_injective, Qr.card_eq_multiplicity,
      ← natCard_subgroupOf_of_le' (sigmaCore_le M),
      _root_.CFSG.FeitThompson.Proofs.factorization_natCard_eq_of_isHallPiSubgroup hrp hHall hrσ]
  have hQnorm : M ≤ normalizer
      (((Qr : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype : Subgroup G) : Set G) := by
    have : (Qr : Subgroup ↥(sigmaCore M)).Characteristic := sylow_characteristic_of_isNilpotent Qr
    exact le_normalizer_map_subtype_of_characteristic _ (le_normalizer_sigmaCore M)
  have hQnormal :
      (((Qr : Subgroup ↥(sigmaCore M)).map (sigmaCore M).subtype).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer hQM hQnorm
  have h1lt : 1 < Nat.card ↥X :=
    lt_of_le_of_ne Nat.card_pos (Ne.symm fun h => hsetup.ne_bot (Subgroup.card_eq_one.1 h))
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 h1lt
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨w, hwX, hwo⟩ := exists_mem_orderOf_eq_of_dvd hpp (Nat.dvd_of_mem_primeFactors hp)
  have hPcard : Nat.card ↥(zpowers w) = p := by rw [Nat.card_zpowers, hwo]
  have hPp : IsPGroup p ↥(zpowers w) := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hPX : (zpowers w : Subgroup G) ≤ X := zpowers_le.2 hwX
  have hPF : (zpowers w : Subgroup G) ≤ (fittingRaw ↥M).map M.subtype := by
    rw [← mixedFitting_eq]
    exact hPX.trans hsetup.le
  have hpσ : p ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le (hPX.trans hXS)) p
      (Nat.mem_primeFactors.2 ⟨hpp, hPcard ▸ dvd_rfl, by rw [hPcard]; exact hpp.pos.ne'⟩)
  have hCM : centralizer ((zpowers w : Subgroup G) : Set G) ≤ M :=
    centralizer_le_of_natCard_eq_prime_of_le_fitting hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable hsetup.isCoatom hr hQM hQnormal hQcard hpp hPF hPcard
  have hPM : (zpowers w : Subgroup G) ≤ MulAut.conj (1 : G) • M := by
    simpa using hPX.trans hXM
  have hPMg : (zpowers w : Subgroup G) ≤ MulAut.conj g⁻¹ • M := by
    have hXc : X ≤ conjSubgroup (mixedFitting M) g := hsetup.eq ▸ inf_le_right
    refine (hPX.trans hXc).trans ?_
    rw [conjSubgroup_eq, conj_smul_eq_map_conj]
    exact Subgroup.map_mono (mixedFitting_le M)
  obtain ⟨c, hc, hconj⟩ := exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable hsetup.isCoatom hpσ hPp hPM hPMg
  have hcfix : MulAut.conj c • M = M :=
    mem_normalizer_iff_conj_smul_eq.1 (M.le_normalizer (hCM hc))
  have hgM : MulAut.conj g⁻¹ • M = M := by
    rw [← hconj]
    simpa using hcfix
  refine hsetup.notMem ?_
  have hg' : g ∈ normalizer (M : Set G) := by
    simpa using (normalizer (M : Set G)).inv_mem (mem_normalizer_iff_conj_smul_eq.2 hgM)
  rwa [normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hsetup.isCoatom] at hg'

theorem commutator_le_mixedFitting_of_betaPrimes_eq_empty
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hM : IsCoatom M) (hβ : betaPrimes ↥M = ∅) :
    (⁅M, M⁆ : Subgroup G) ≤ mixedFitting M := by
  have hGp : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hquot := _root_.CFSG.FeitThompson.Proofs.isNilpotent_quotient_piCore_commutator h₄ hGp hM
  have heq : piCore (betaPrimes ↥M) ↥(⁅M, M⁆ : Subgroup G) = ⊥ := by
    rw [hβ]; exact piCore_empty _
  have h1 : Group.IsNilpotent
      (↥(⁅M, M⁆ : Subgroup G) ⧸ (⊥ : Subgroup ↥(⁅M, M⁆ : Subgroup G))) :=
    Group.nilpotent_of_mulEquiv (_h := hquot) (QuotientGroup.quotientMulEquivOfEq heq)
  have hnil : Group.IsNilpotent ↥(⁅M, M⁆ : Subgroup G) :=
    Group.nilpotent_of_mulEquiv (_h := h1) QuotientGroup.quotientBot
  rw [mixedFitting_eq]
  exact le_map_fittingRaw_of_le_normalizer (Subgroup.commutator_le_self M)
    (_root_.CFSG.FeitThompson.Proofs.le_normalizer_commutator_self M) hnil

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson Subgroup

universe u

theorem FBG_nonti_fitting_nilpotent_core_and_beta_exclusion
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_nonti_fitting_nilpotent_core_and_beta_exclusion.{u} := by
  intro G _ _ hG M X g hsetup Y hY
  have hSnil : Group.IsNilpotent ↥(sigmaCore M) :=
    isNilpotent_sigmaCore_of_isFittingOverlapSetup h₂ hG hsetup
  obtain ⟨hHM, -, hYcyc, hYτ, hprod, -, -, -, -⟩ := h₁ G hG M hsetup.isCoatom hSnil Y hY
  have hfin : Fintype G := Fintype.ofFinite G
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) :=
    (h₃ G hG2 M hsetup.isCoatom).1.2
  have hXS : X ≤ sigmaCore M :=
    le_sigmaCore_of_isFittingOverlapSetup hG hsetup hHall hprod hYcyc
  have hβ : betaPrimes ↥M = ∅ :=
    betaPrimes_eq_empty_of_isFittingOverlapSetup hG hsetup hSnil hHall hXS
  exact ⟨hSnil, hHM, hXS, hβ,
    commutator_le_mixedFitting_of_betaPrimes_eq_empty h₄ hG hsetup.isCoatom hβ,
    hprod, hYcyc, hYτ⟩

end

end CFSG.FeitThompson.Proofs
