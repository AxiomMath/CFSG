module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PLengthOneNarrowSylowNormalComplement
import CFSG.FeitThompson.Local.PElementNormalSubgroupPLength
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.PrimeCentralizerTransitiveHyperplanes
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Foundations.NormalHallIntersectionHall
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

variable {G : Type u} [Group G] {p : ℕ}

section Aux

variable [Finite G]

theorem normal_subgroupOf_prep06_pComplCoreIn (p : ℕ) (X : Subgroup G) :
    ((Prep06.pComplCoreIn p X).subgroupOf X).Normal := by
  rw [Prep06.pComplCoreIn_eq, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact pComplCore_normal p ↥X

theorem not_dvd_natCard_prep06_pComplCoreIn (hp : p.Prime) (X : Subgroup G) :
    ¬ p ∣ Nat.card (Prep06.pComplCoreIn p X) := by
  rw [Prep06.pComplCoreIn_eq, Subgroup.card_map_of_injective X.subtype_injective]
  exact not_dvd_natCard_pComplCore hp _

theorem relIndex_prep06_pComplCoreIn (p : ℕ) (X : Subgroup G) :
    (Prep06.pComplCoreIn p X).relIndex X = (pComplCore p ↥X).index := by
  rw [Prep06.pComplCoreIn_eq]; exact relIndex_map_subtype _

theorem le_prep06_pComplCoreIn {X N : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set G)) (hpN : ¬ p ∣ Nat.card N) :
    N ≤ Prep06.pComplCoreIn p X := by
  rw [Prep06.pComplCoreIn_eq, ← CFSG.FeitThompson.pComplCoreIn_eq]
  exact le_pComplCoreIn hNX hnorm hpN

theorem relIndex_dvd_relIndex_of_normal {K S W : Subgroup G} (hSW : S ≤ W)
    (hK : (K.subgroupOf W).Normal) : K.relIndex S ∣ K.relIndex W := by
  have := hK
  have h := index_inf_subgroupOf_dvd_index (X := ↥W) (K.subgroupOf W) (S.subgroupOf W)
  rwa [index_inf_subgroupOf, Subgroup.relIndex_subgroupOf hSW] at h

end Aux

theorem normal_inf_subgroupOf_of_le {K S W : Subgroup G} (hKW : K ≤ W) (hSW : S ≤ W)
    (hK : (K.subgroupOf W).Normal) : ((K ⊓ S).subgroupOf S).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 fun g hg => ?_
  have hgK : g ∈ normalizer (K : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKW).1 hK) (hSW hg)
  rw [Subgroup.mem_normalizer_iff] at hgK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, ← hgK h]
  refine and_congr Iff.rfl ⟨fun hh => S.mul_mem (S.mul_mem hg hh) (S.inv_mem hg), fun hh => ?_⟩
  have he : h = g⁻¹ * (g * h * g⁻¹) * g := by group
  rw [he]
  exact S.mul_mem (S.mul_mem (S.inv_mem hg) hh) hg

theorem exists_sylow_isPNarrow {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (h : p ∉ betaPrimes X) : ∃ P : Sylow p X, IsPNarrow p ↥(P : Subgroup X) := by
  have := Fact.mk hp
  by_cases hd : p ∣ Nat.card X
  · by_contra hc
    exact h (mem_betaPrimes_iff.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩,
      fun P hP => hc ⟨P, hP⟩⟩)
  · exact ⟨Classical.arbitrary _, isPNarrow_of_not_dvd_card hp fun hdd =>
      hd (hdd.trans (Subgroup.card_subgroup_dvd_card _))⟩

noncomputable def commutatorEquiv (M : Subgroup G) :
    ↥(_root_.commutator ↥M) ≃* ↥(⁅M, M⁆ : Subgroup G) :=
  ((_root_.commutator ↥M).equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator M))

theorem exists_relIndex_derived_eq_pow [Finite G]
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G)
    {M : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hodd : Odd p)
    (hbeta : p ∉ betaPrimes ↥M) :
    ∃ n, (Prep06.pComplCoreIn p (⁅M, M⁆ : Subgroup G)).relIndex ⁅M, M⁆ = p ^ n := by
  have hMne : M ≠ ⊤ := hM.1
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hMne
  have hoddM : Odd (Nat.card ↥M) := hG.odd_natCard.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hlen : HasPLengthLeOne p ↥M := by
    have := Fact.mk hp
    rw [hasPLengthLeOne_iff_not_dvd_index]
    have h := h₂ G hG p hp M hMne
    rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  obtain ⟨P, hP⟩ := exists_sylow_isPNarrow hp hbeta
  have hcompl := isNormalPComplement_pComplCore_commutator hp hodd hoddM P hP hlen
  have heq := (hcompl.map_mulEquiv (commutatorEquiv M)).eq_pComplCore hp
  obtain ⟨n, hn⟩ := (isNormalPComplement_iff.1 hcompl).2.2
  refine ⟨n, ?_⟩
  rw [relIndex_prep06_pComplCoreIn, ← heq, Subgroup.index_map_equiv, hn]

theorem exists_relIndex_sigmaCore_eq_pow [Finite G]
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G)
    {M : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hodd : Odd p)
    (hbeta : p ∉ betaPrimes ↥M) (hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    ∃ k, (Prep06.pComplCoreIn p (sigmaCore M)).relIndex (sigmaCore M) = p ^ k := by
  obtain ⟨n, hn⟩ := exists_relIndex_derived_eq_pow h₂ hG hM hp hodd hbeta
  set K : Subgroup G := Prep06.pComplCoreIn p (⁅M, M⁆ : Subgroup G) with hK
  have hKnorm : (K.subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
    normal_subgroupOf_prep06_pComplCoreIn _ _
  have hKle : K ≤ (⁅M, M⁆ : Subgroup G) := by
    rw [hK, Prep06.pComplCoreIn_eq]; exact Subgroup.map_subtype_le _
  have hInfNormal : ((K ⊓ sigmaCore M).subgroupOf (sigmaCore M)).Normal :=
    normal_inf_subgroupOf_of_le hKle hSM hKnorm
  have hle1 : K ⊓ sigmaCore M ≤ K := inf_le_left
  have hle2 : K ⊓ sigmaCore M ≤ sigmaCore M := inf_le_right
  have hInfCard : ¬ p ∣ Nat.card ↥(K ⊓ sigmaCore M) := fun hd =>
    not_dvd_natCard_prep06_pComplCoreIn hp (⁅M, M⁆ : Subgroup G)
      (hd.trans (Subgroup.card_dvd_of_le hle1))
  have hInfLe : K ⊓ sigmaCore M ≤ Prep06.pComplCoreIn p (sigmaCore M) :=
    le_prep06_pComplCoreIn hle2
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle2).1 hInfNormal) hInfCard
  have hdvd : (Prep06.pComplCoreIn p (sigmaCore M)).relIndex (sigmaCore M) ∣ p ^ n := by
    refine dvd_trans (Subgroup.relIndex_dvd_of_le_left (sigmaCore M) hInfLe) ?_
    rw [Subgroup.inf_relIndex_right, ← hn]
    exact relIndex_dvd_relIndex_of_normal hSM hKnorm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨k, hk⟩

theorem FTS_beta_prime_derived_complement
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_beta_prime_derived_complement.{u} := by
  intro G _ _ hG M hM p hp hodd hbeta
  have hMc : IsCoatom M := hM
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hSM : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G) := (h₁ G hG2 M hMc).2.2
  exact ⟨normal_subgroupOf_prep06_pComplCoreIn _ _,
    not_dvd_natCard_prep06_pComplCoreIn hp _,
    exists_relIndex_derived_eq_pow h₂ hG8 hMc hp hodd hbeta,
    normal_subgroupOf_prep06_pComplCoreIn _ _,
    not_dvd_natCard_prep06_pComplCoreIn hp _,
    exists_relIndex_sigmaCore_eq_pow h₂ hG8 hMc hp hodd hbeta hSM⟩

end

end CFSG.FeitThompson.Proofs
