module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimeDerivedComplement
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
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

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] {p q : ℕ}

section Aux

variable [Finite G]

theorem prep06_pComplCoreIn_eq (p : ℕ) (X : Subgroup G) :
    Prep06.pComplCoreIn p X = CFSG.FeitThompson.pComplCoreIn p X := by
  rw [CFSG.FeitThompson.pComplCoreIn_eq]; rfl

theorem isPiSubgroup_of_isPGroup {π : Set ℕ} {S : Subgroup G} (hq : q.Prime)
    (hqπ : q ∈ π) (hS : IsPGroup q ↥S) : IsPiSubgroup π S := by
  have := Fact.mk hq
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  refine isPiSubgroup_iff.2 fun r hr => ?_
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hdvd := Nat.dvd_of_mem_primeFactors hr
  rw [hn] at hdvd
  exact ((Nat.prime_dvd_prime_iff_eq hrp hq).1 (hrp.dvd_of_dvd_pow hdvd)) ▸ hqπ

theorem le_of_isHallPiSubgroup_subgroupOf {π : Set ℕ} {K S X : Subgroup G} (hKX : K ≤ X)
    (hnorm : (K.subgroupOf X).Normal) (hHall : IsHallPiSubgroup π (K.subgroupOf X))
    (hSX : S ≤ X) (hS : IsPiSubgroup π S) : S ≤ K := by
  have := hnorm
  have hSπ : IsPiSubgroup π (S.subgroupOf X) :=
    isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hS r
      (by rwa [natCard_subgroupOf_of_le hSX] at hr)
  have h' := Subgroup.map_mono (f := X.subtype) (hHall.le_of_isPiSubgroup hSπ)
  rwa [Subgroup.map_subgroupOf_eq_of_le hSX, Subgroup.map_subgroupOf_eq_of_le hKX] at h'

theorem coe_eq_mul_of_normalizer_le (hq : q.Prime) {T D S M : Subgroup G}
    (hDT : D ≤ T) (hnorm : T ≤ normalizer (D : Set G)) (hSD : S ≤ D)
    (hS : Nat.card ↥S = q ^ (Nat.card ↥D).factorization q)
    (hNM : normalizer (S : Set G) ≤ M) :
    (T : Set G) = (D : Set G) * ((M ⊓ T : Subgroup G) : Set G) := by
  have := Fact.mk hq
  have hST : S ≤ T := hSD.trans hDT
  have hDn : (D.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hDT hnorm
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨r, hr, n, hn, hrn⟩ := exists_mem_mul_mem_normalizer (X := ↥T)
      (R := D.subgroupOf T) (P := S.subgroupOf T) (p := q)
      (fun y hy => Subgroup.mem_subgroupOf.2 (hSD (Subgroup.mem_subgroupOf.1 hy)))
      (by rw [natCard_subgroupOf_of_le hST, hS, natCard_subgroupOf_of_le hDT])
      (⟨x, hx⟩ : ↥T)
    rw [← Subgroup.subgroupOf_normalizer_eq hST] at hn
    have hx' : x = (r : G) * (n : G) := congrArg (fun y : ↥T => (y : G)) hrn
    exact ⟨(r : G), Subgroup.mem_subgroupOf.1 hr, (n : G),
      ⟨hNM (Subgroup.mem_subgroupOf.1 hn), n.2⟩, hx'.symm⟩
  · rintro x ⟨d, hd, m, hm, rfl⟩
    exact T.mul_mem (hDT hd) hm.2

theorem notMem_sigmaPrimes_of_dvd_natCard_complement {M E : Subgroup G}
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (hp : p.Prime) (hpE : p ∣ Nat.card ↥E) : p ∉ sigmaPrimes M := by
  intro hmem
  have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hsd.natCard_eq_mul
  have h1 : Nat.card ↥((sigmaCore M).subgroupOf M) * ((sigmaCore M).subgroupOf M).index
      = Nat.card ↥M := Subgroup.card_mul_index _
  rw [natCard_subgroupOf_of_le (sigmaCore_le M), hcard] at h1
  have hidx : ((sigmaCore M).subgroupOf M).index = Nat.card ↥E :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  exact hHall.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨hp, hidx ▸ hpE, by rw [hidx]; exact Nat.card_pos.ne'⟩) hmem

end Aux

theorem FBG_sigma_prime_normalizer_common_sigma_prime_factor
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_sigma_prime_normalizer_common_sigma_prime_factor.{u} := by
  intro G _ _ hG M T hM hT hMT q hq hqM Y hYM hYbot hYq hYT E hE p hp hpE hpβ hqT D hD
  have hsimple := hG.isSimpleGroup
  have hG06 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨⟨-, hHallM⟩, -, -⟩ := h₁ G hG M hM
  obtain ⟨⟨-, hHallT⟩, -, hSTle⟩ := h₁ G hG T hT
  have hpσM : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_dvd_natCard_complement hHallM hE hp hpE
  have hpq : p ≠ q := fun h => hpσM (h ▸ hqM)
  have hpodd : Odd p := by
    refine hp.odd_of_ne_two fun h => ?_
    have h2 : (2 : ℕ) ∣ Nat.card G :=
      h ▸ (hpE.trans (Subgroup.card_dvd_of_le hE.right_le)).trans
        (Subgroup.card_subgroup_dvd_card M)
    exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2 h2)
  have hpβT : p ∉ betaPrimes ↥T := by
    rw [betaPrimes_subgroup_eq_sigmaPrimes_inter hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hT]
    exact fun hmem => hpβ hmem.2
  have hDle : D ≤ (⁅T, T⁆ : Subgroup G) :=
    hD ▸ CFSG.FeitThompson.pComplCoreIn_le _ _
  have hDT : D ≤ T := hDle.trans (Subgroup.commutator_le_self T)
  have hDnormT : T ≤ normalizer (D : Set G) := by
    rw [hD]
    exact le_normalizer_pComplCoreIn_of_le_normalizer p
      (le_normalizer_commutator_self (Subgroup.le_normalizer (H := T)))
  have hDnorm : (D.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hDT hDnormT
  have hpD : ¬ p ∣ Nat.card ↥D := by
    rw [hD]; exact not_dvd_natCard_pComplCoreIn hp _
  refine ⟨hDnorm, hpD, ?_⟩
  obtain ⟨hDn', -, ⟨k, hk⟩, -, -, -⟩ :=
    FTS_beta_prime_derived_complement h₁ h₃ G hG06 T hT p hp hpodd hpβT
  rw [prep06_pComplCoreIn_eq, ← hD] at hDn' hk
  have hYTle : Y ≤ T := Subgroup.le_normalizer.trans hYT
  obtain ⟨S, hYS, hS⟩ := exists_isSylowSubgroupOf_ge hq (le_inf hYM hYTle) hYq
  obtain ⟨-, hemb, -⟩ := FBG_sigma_prime_normalizer_embedding_sylows h₂ G hG M T hM hT hMT q hq hqM
    Y hYM hYbot hYq hYT
  obtain ⟨hNM, hST⟩ := hemb S hS hYS
  have hSq : IsPGroup q ↥S := IsPGroup.of_card hST.2
  have hSsigma : S ≤ sigmaCore T :=
    le_of_isHallPiSubgroup_subgroupOf (sigmaCore_le T) (sigmaCore_normal_subgroupOf T) hHallT
      hST.1 (isPiSubgroup_of_isPGroup hq hqT hSq)
  have hScomm : S ≤ (⁅T, T⁆ : Subgroup G) := hSsigma.trans hSTle
  have hHallD : IsHallPiSubgroup {r : ℕ | r ≠ p} (D.subgroupOf (⁅T, T⁆ : Subgroup G)) := by
    constructor
    · refine isPiSubgroup_iff.2 fun r hr => ?_
      rw [natCard_subgroupOf_of_le hDle] at hr
      exact fun (hrp : r = p) => hpD (hrp ▸ Nat.dvd_of_mem_primeFactors hr)
    · intro r hr
      rw [show (D.subgroupOf (⁅T, T⁆ : Subgroup G)).index = p ^ k from hk] at hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hre : r = p := (Nat.prime_dvd_prime_iff_eq hrp hp).1
        (hrp.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hr))
      simpa using hre
  have hSD : S ≤ D :=
    le_of_isHallPiSubgroup_subgroupOf hDle hDn' hHallD hScomm
      (isPiSubgroup_of_isPGroup hq (by simpa using Ne.symm hpq) hSq)
  have hSylowD : Nat.card ↥S = q ^ (Nat.card ↥D).factorization q := by
    have h1 : (Nat.card ↥T).factorization q ≤ (Nat.card ↥D).factorization q :=
      (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        (hST.2 ▸ Subgroup.card_dvd_of_le hSD)
    have h2 : (Nat.card ↥D).factorization q ≤ (Nat.card ↥T).factorization q :=
      (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
        ((Nat.ordProj_dvd _ q).trans (Subgroup.card_dvd_of_le hDT))
    rw [hST.2, le_antisymm h1 h2]
  exact coe_eq_mul_of_normalizer_le hq hDT hDnormT hSD hSylowD hNM

end

end CFSG.FeitThompson.Proofs
