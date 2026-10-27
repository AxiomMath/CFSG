module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.BetaNormalPrimeCentralizerPosition
import CFSG.FeitThompson.Local.LargeAbelianNormalNoComplementaryPrime
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.LargestPrimeCharacteristicSylow
import CFSG.FeitThompson.Local.BetaSubgroupNormalizerInMaximal
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
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

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G]

theorem normal_subgroupOf_pCoreIn (s : ℕ) (H : Subgroup G) :
    ((CFSG.FeitThompson.pCoreIn s H).subgroupOf H).Normal := by
  rw [CFSG.FeitThompson.pCoreIn_eq, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact CFSG.FeitThompson.pCore_normal s ↥H

theorem pCoreIn_conj_smul (s : ℕ) (H : Subgroup G) (c : G) :
    CFSG.FeitThompson.pCoreIn s (MulAut.conj c • H) = MulAut.conj c • CFSG.FeitThompson.pCoreIn s H := by
  rw [CFSG.FeitThompson.pCoreIn_eq, CFSG.FeitThompson.pCoreIn_eq,
    conj_smul_eq_map_conj, conj_smul_eq_map_conj, map_map_pCore_comm (MulAut.conj c) H s]

theorem exists_prime_pCoreIn_ne_bot_of_isSolvable {H : Subgroup G} (hsolv : Group.IsSolvable ↥H)
    (hH : H ≠ ⊥) : ∃ s : ℕ, s.Prime ∧ CFSG.FeitThompson.pCoreIn s H ≠ ⊥ := by
  have := hsolv
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact hH (eq_bot_of_forall_pCoreIn_eq_bot fun r hr => hcon r hr)

omit [Finite G] in
theorem conj_smul_ne_bot {Y : Subgroup G} (c : G) (h : Y ≠ ⊥) : MulAut.conj c • Y ≠ ⊥ := fun hc =>
  h (by simpa [smul_smul] using congrArg (fun Z => MulAut.conj c⁻¹ • Z) hc)

theorem exists_isHallPiSubgroupOf_ge_of_isPiSubgroup {π : Set ℕ} {X U : Subgroup G}
    (hsolv : Group.IsSolvable ↥X) (hUX : U ≤ X) (hU : IsPiSubgroup π U) :
    ∃ H : Subgroup G, IsHallPiSubgroupOf π H X ∧ U ≤ H := by
  have := hsolv
  have hU' : IsPiSubgroup π (U.subgroupOf X) := by
    refine isPiSubgroup_iff.2 fun p hp => isPiSubgroup_iff.1 hU p ?_
    rwa [natCard_subgroupOf_of_le hUX] at hp
  obtain ⟨H', hH', hUH'⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hU'
  refine ⟨H'.map X.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    exact isHallSubgroup_iff_isHallPiSubgroup.1 hH'
  · calc U = (U.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hUX).symm
      _ ≤ H'.map X.subtype := Subgroup.map_mono hUH'

theorem exists_mem_conj_smul_eq_of_isHallPiSubgroupOf {π : Set ℕ} {X H K : Subgroup G}
    (hsolv : Group.IsSolvable ↥X) (hH : IsHallPiSubgroupOf π H X)
    (hK : IsHallPiSubgroupOf π K X) : ∃ c ∈ X, MulAut.conj c • H = K := by
  have := hsolv
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup
    (isHallSubgroup_iff_isHallPiSubgroup.2 hH.2) (isHallSubgroup_iff_isHallPiSubgroup.2 hK.2)
  have hgH : (MulAut.conj (g : G) • H).subgroupOf X = K.subgroupOf X := by
    rw [CFSG.FeitThompson.conj_smul_subgroupOf hH.1 g, hg]
  have hle : MulAut.conj (g : G) • H ≤ X := by
    intro x hx
    have hx' : (g : G)⁻¹ * x * g ∈ H := mem_conj_smul_iff.1 hx
    have hxeq : x = (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ := by group
    rw [hxeq]
    exact X.mul_mem (X.mul_mem g.2 (hH.1 hx')) (X.inv_mem g.2)
  exact ⟨g, g.2, le_antisymm (le_of_subgroupOf_le hle hgH.le)
    (le_of_subgroupOf_le hK.1 hgH.ge)⟩

theorem dvd_natCard_of_isHallPiSubgroupOf {π : Set ℕ} {H X : Subgroup G}
    (hH : IsHallPiSubgroupOf π H X) {r : ℕ} (hr : r.Prime) (hrπ : r ∈ π)
    (hrX : r ∣ Nat.card ↥X) : r ∣ Nat.card ↥H := by
  by_contra hrH
  have hprod : Nat.card ↥(H.subgroupOf X) * (H.subgroupOf X).index = Nat.card ↥X :=
    Subgroup.card_mul_index _
  have hcard : Nat.card ↥(H.subgroupOf X) = Nat.card ↥H := natCard_subgroupOf_of_le hH.1
  have hdvd : r ∣ (H.subgroupOf X).index := by
    refine (hr.dvd_mul.1 (hprod ▸ hrX)).resolve_left ?_
    rwa [hcard]
  exact hH.2.notMem_of_mem_primeFactors_index r
    (Nat.mem_primeFactors.2 ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrπ

theorem exists_isHallPiSubgroupOf_ge_pCoreIn_ne_bot {π : Set ℕ} {C H₀ U : Subgroup G}
    (hsolv : Group.IsSolvable ↥C) (hH₀ : IsHallPiSubgroupOf π H₀ C) (hUC : U ≤ C)
    (hU : IsPiSubgroup π U) {s : ℕ} (hs : CFSG.FeitThompson.pCoreIn s H₀ ≠ ⊥) :
    ∃ H : Subgroup G, IsHallPiSubgroupOf π H C ∧ U ≤ H ∧ CFSG.FeitThompson.pCoreIn s H ≠ ⊥ := by
  obtain ⟨K, hK, hUK⟩ := exists_isHallPiSubgroupOf_ge_of_isPiSubgroup hsolv hUC hU
  obtain ⟨c, -, hconj⟩ := exists_mem_conj_smul_eq_of_isHallPiSubgroupOf hsolv hH₀ hK
  refine ⟨K, hK, hUK, ?_⟩
  rw [← hconj, pCoreIn_conj_smul]
  exact conj_smul_ne_bot c hs

theorem centralizer_ne_top (hG : IsFBGAmbient G) {P : Subgroup G} (hP : P ≠ ⊥) :
    (centralizer (P : Set G) : Subgroup G) ≠ ⊤ := by
  have := hG.isSimpleGroup
  obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP
  have h1 : (centralizer (P : Set G) : Subgroup G) ≤ centralizer {x} :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx)
  exact fun hc => (centralizer_singleton_lt_top hG.not_isMulCommutative hx1).ne
    (top_le_iff.1 (hc ▸ h1))

theorem exists_mem_betaPrimes_dvd {L₀ Y : Subgroup G} (hY : Y ≤ betaCore L₀) (hYne : Y ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ r ∈ betaPrimes ↥L₀ ∧ r ∣ Nat.card ↥Y := by
  have : Nontrivial ↥Y := Y.nontrivial_iff_ne_bot.2 hYne
  obtain ⟨r, hr⟩ := primeFactors_natCard_nonempty ↥Y
  refine ⟨r, Nat.prime_of_mem_primeFactors hr, ?_, Nat.dvd_of_mem_primeFactors hr⟩
  exact isPiSubgroup_iff.1 ((isPiSubgroup_betaCore L₀).of_le hY) r hr

theorem exists_hall_position_of_mem_betaPrimes
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsFBGAmbient G) {π : Set ℕ}
    {M₀ L₀ P H₀ : Subgroup G} (hM₀ : IsCoatom M₀) (hPM₀ : P ≤ M₀) (hP : P ≠ ⊥)
    (hBM₀ : betaCore M₀ ⊓ (centralizer (P : Set G) : Subgroup G) ≠ ⊥)
    (hBL₀ : betaCore L₀ ⊓ (centralizer (P : Set G) : Subgroup G) ≠ ⊥)
    (hπM₀ : betaPrimes ↥M₀ ⊆ π) (hπL₀ : betaPrimes ↥L₀ ⊆ π)
    (hsolv : Group.IsSolvable ↥(centralizer (P : Set G) : Subgroup G))
    (hH₀ : IsHallPiSubgroupOf π H₀ (centralizer (P : Set G)))
    {s : ℕ} (hs : s.Prime) (hsM₀ : s ∈ betaPrimes ↥M₀)
    (hcore : CFSG.FeitThompson.pCoreIn s H₀ ≠ ⊥) :
    ∃ H : Subgroup G, H ≤ (centralizer (P : Set G) ⊓ M₀ : Subgroup G) ∧
      ∃ s' r : ℕ, s' ∈ betaPrimes ↥M₀ ∧ r ∈ betaPrimes ↥L₀ ∧
        IsHallPiSubgroupOf π H (centralizer (P : Set G)) ∧
        betaCore M₀ ⊓ (centralizer (P : Set G) : Subgroup G) ≤ H ∧
        r ∣ Nat.card ↥H ∧
        CFSG.FeitThompson.pCoreIn s' H ≠ ⊥ ∧ ((CFSG.FeitThompson.pCoreIn s' H).subgroupOf H).Normal ∧
        CFSG.FeitThompson.pCoreIn s' H ≤ betaCore M₀ := by
  have hFact : Fact s.Prime := ⟨hs⟩
  obtain ⟨H, hH, hUH, hHcore⟩ :=
    exists_isHallPiSubgroupOf_ge_pCoreIn_ne_bot hsolv hH₀ inf_le_right
      (((isPiSubgroup_betaCore M₀).of_le inf_le_left).mono hπM₀) hcore
  obtain ⟨hHM₀, hXB⟩ :=
    FBG_beta_normal_prime_centralizer_position.{u} h₁ h₂ G hG M₀ hM₀ P hPM₀ hP hBM₀ H hH.1 hUH
      s hsM₀ hs (CFSG.FeitThompson.pCoreIn s H) (CFSG.FeitThompson.pCoreIn_le s H)
      (normal_subgroupOf_pCoreIn s H) hHcore
      (IsPGroup.iff_card.1 (isPGroup_pCoreIn hs H))
  obtain ⟨r, hr, hrβ, hrY⟩ := exists_mem_betaPrimes_dvd (L₀ := L₀) inf_le_left hBL₀
  exact ⟨H, le_inf hH.1 hHM₀, s, r, hsM₀, hrβ, hH, hUH,
    dvd_natCard_of_isHallPiSubgroupOf hH hr (hπL₀ hrβ)
      (hrY.trans (Subgroup.card_dvd_of_le inf_le_right)),
    hHcore, normal_subgroupOf_pCoreIn s H, hXB⟩

theorem FBG_two_beta_fixed_cores_hall_position
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_two_beta_fixed_cores_hall_position.{u} := by
  intro G _ _ hG M L hM hL _ P hPML hP hBM hBL
  have hG' : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set π : Set ℕ := betaPrimes ↥M ∪ betaPrimes ↥L with hπ
  set C : Subgroup G := centralizer (P : Set G) with hC
  have hsolv : Group.IsSolvable ↥C :=
    hG.isSolvable_of_ne_top C (centralizer_ne_top hG' hP)
  obtain ⟨H₀, hH₀, hUH₀⟩ :=
    exists_isHallPiSubgroupOf_ge_of_isPiSubgroup (π := π) (U := betaCore M ⊓ C) hsolv inf_le_right
      (((isPiSubgroup_betaCore M).of_le inf_le_left).mono Set.subset_union_left)
  have hH₀ne : H₀ ≠ ⊥ := fun hb => hBM (le_bot_iff.1 (hb ▸ hUH₀))
  obtain ⟨s, hs, hcore⟩ :=
    exists_prime_pCoreIn_ne_bot_of_isSolvable (isSolvable_of_le (K := C) hH₀.1) hH₀ne
  have hsπ : s ∈ π := by
    have hdvd : s ∣ Nat.card ↥H₀ :=
      (prime_dvd_natCard_of_isPGroup hs hcore (isPGroup_pCoreIn hs H₀)).trans
        (Subgroup.card_dvd_of_le (CFSG.FeitThompson.pCoreIn_le s H₀))
    exact isPiSubgroup_iff.1 hH₀.isPiSubgroup s
      (Nat.mem_primeFactors.2 ⟨hs, hdvd, Nat.card_pos.ne'⟩)
  rcases hsπ with hsM | hsL
  · obtain ⟨H, hHle, s', r, hs'β, hrβ, hHall, hUH, hrH, hXne, hXnorm, hXB⟩ :=
      exists_hall_position_of_mem_betaPrimes h₁ h₂ hG' hM (le_inf_iff.1 hPML).1 hP hBM hBL
        Set.subset_union_left Set.subset_union_right hsolv hH₀ hs hsM hcore
    exact ⟨M, L, Or.inl ⟨rfl, rfl⟩, H, hHle, s', r, hs'β, hrβ, hHall, hUH, hrH, hXne, hXnorm, hXB⟩
  · obtain ⟨H, hHle, s', r, hs'β, hrβ, hHall, hUH, hrH, hXne, hXnorm, hXB⟩ :=
      exists_hall_position_of_mem_betaPrimes h₁ h₂ hG' hL (le_inf_iff.1 hPML).2 hP hBL hBM
        Set.subset_union_right Set.subset_union_left hsolv hH₀ hs hsL hcore
    exact ⟨L, M, Or.inr ⟨rfl, rfl⟩, H, hHle, s', r, hs'β, hrβ, hHall, hUH, hrH, hXne, hXnorm, hXB⟩

end

end CFSG.FeitThompson.Proofs
