module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.Tau13NonregularLineNormalizerSigma
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.KappaResidualLocalNormalizer
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.NormalProductCoprimeNormalizerFactorization
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.PComplCoreCentralizerInAmbient
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
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
open CFSG.FeitThompson.Prep03

universe u

variable {G : Type u} [Group G]

theorem sup_eq_of_isSemidirect [Finite G] {M K U : Subgroup G}
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) :
    (sigmaCore M ⊔ U) ⊔ K = M := by
  rw [sup_assoc]; exact hdec.2.2.2.1

theorem le_normalizer_sigmaCore_sup [Finite G] {M K U : Subgroup G}
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) (hdecE : IsSemidirect (U ⊔ K) U K) :
    M ≤ normalizer ((sigmaCore M ⊔ U : Subgroup G) : Set G) := by
  have h : (sigmaCore M ⊔ U) ⊔ K ≤ normalizer ((sigmaCore M ⊔ U : Subgroup G) : Set G) := by
    refine sup_le Subgroup.le_normalizer (fun g hg => ?_)
    exact CFSG.FeitThompson.mem_normalizer_sup
      (hdec.2.2.1 (hdec.2.1 (hdecE.2.1 hg))) (hdecE.2.2.1 (hdecE.2.1 hg))
  rwa [sup_eq_of_isSemidirect hdec] at h

theorem natCard_sigmaCore_sup_eq [Finite G] {M K U : Subgroup G}
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) (hdecE : IsSemidirect (U ⊔ K) U K) :
    Nat.card ↥(sigmaCore M ⊔ U) = Nat.card ↥(sigmaCore M) * Nat.card ↥U := by
  have hUM : U ≤ M := le_trans hdecE.1 hdec.2.1
  have hUS : U ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) := hUM.trans hdec.2.2.1
  have hSU : sigmaCore M ⊓ U = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ (le_sup_left : U ≤ U ⊔ K)).trans hdec.2.2.2.2.le)
  have h := CFSG.FeitThompson.natCard_mul_mul_natCard_inf (sigmaCore M) U
  rw [hSU, ← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hUS] at h
  simpa using h

theorem coprime_natCard_sigmaCore_sup [Finite G] {M K U : Subgroup G}
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) (hdecE : IsSemidirect (U ⊔ K) U K)
    (hU : IsHallPiOf (sigmaPrimes M ∪ kappaPrimes M)ᶜ U M)
    (hK : IsHallPiOf (kappaPrimes M) K M) :
    Nat.Coprime (Nat.card ↥(sigmaCore M ⊔ U)) (Nat.card ↥K) := by
  refine (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').1
    (Finset.disjoint_left.2 fun q hq hq' => ?_)
  have hqκ : q ∈ kappaPrimes M := hK.2.1 q hq'
  rw [natCard_sigmaCore_sup_eq hdec hdecE, Nat.primeFactors_mul Nat.card_pos.ne'
    Nat.card_pos.ne'] at hq
  rcases Finset.mem_union.1 hq with h | h
  · exact (mem_kappaPrimes_iff.1 hqκ).2.2.1
      (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q h)
  · exact hU.2.1 q h (Or.inr hqκ)

theorem inf_centralizer_sup_eq [Finite G] {M K U X : Subgroup G}
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) (hdecE : IsSemidirect (U ⊔ K) U K)
    (hfree : ∀ k ∈ K, k ≠ 1 → cent1 U k = ⊥)
    (hXK : X ≤ K) (hXbot : X ≠ ⊥) :
    (sigmaCore M ⊔ U) ⊓ centralizer (X : Set G) = sigmaCore M ⊓ centralizer (X : Set G) := by
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hXbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxK : x ∈ K := hXK hxX
  have hSU : sigmaCore M ⊓ U = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ (le_sup_left : U ≤ U ⊔ K)).trans hdec.2.2.2.2.le)
  have hUM : U ≤ M := le_trans hdecE.1 hdec.2.1
  have hUS : U ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) := hUM.trans hdec.2.2.1
  have hxS : x ∈ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hdec.2.2.1 (le_trans hdecE.2.1 hdec.2.1 hxK)
  have hxU : x ∈ normalizer (U : Set G) := hdecE.2.2.1 (hdecE.2.1 hxK)
  have hkey := CFSG.FeitThompson.inf_centralizer_singleton_sup_eq
    hSU hxS hxU hUS (hfree x hxK hx1')
  refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_left)
  intro y hy
  obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
  have hmem : y ∈ (sigmaCore M ⊔ U) ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.2 ⟨hyD, by
      rw [Subgroup.mem_centralizer_iff] at hyC ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hyC _ hxX⟩
  exact (Subgroup.mem_inf.1 (hkey ▸ hmem)).1

theorem normalizer_inf_eq_sup [Finite G] {M K U X : Subgroup G}
    (hsolv : Group.IsSolvable ↥M)
    (hdec : IsSemidirect M (sigmaCore M) (U ⊔ K)) (hdecE : IsSemidirect (U ⊔ K) U K)
    (hfree : ∀ k ∈ K, k ≠ 1 → cent1 U k = ⊥)
    (hcop : Nat.Coprime (Nat.card ↥(sigmaCore M ⊔ U)) (Nat.card ↥K))
    (hXK : X ≤ K) (hXbot : X ≠ ⊥) (hKX : K ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ⊓ M = (sigmaCore M ⊓ centralizer (X : Set G)) ⊔ K := by
  have := hsolv
  have hUM : U ≤ M := le_trans hdecE.1 hdec.2.1
  have hKM : K ≤ M := le_trans hdecE.2.1 hdec.2.1
  have hXM : X ≤ M := hXK.trans hKM
  have hDM : sigmaCore M ⊔ U ≤ M := sup_le (sigmaCore_le M) hUM
  have hDnormal : (((sigmaCore M ⊔ U).subgroupOf M).Normal) :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_sigmaCore_sup hdec hdecE)
  have hDJ : (sigmaCore M ⊔ U).subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDM hKM, sup_eq_of_isSemidirect hdec,
      Subgroup.subgroupOf_self]
  have hXJ : X.subgroupOf M ≤ K.subgroupOf M := Subgroup.comap_mono hXK
  have hcop' : Nat.Coprime (Nat.card ↥((sigmaCore M ⊔ U).subgroupOf M))
      (Nat.card ↥(X.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hXK)
  have hform := CFSG.FeitThompson.normalizer_eq_inf_centralizer_sup_inf_normalizer
    (D := (sigmaCore M ⊔ U).subgroupOf M) (J := K.subgroupOf M) (U := X.subgroupOf M)
    hDJ hXJ hcop'
  have hACeq : (sigmaCore M ⊔ U) ⊓ centralizer (X : Set G)
      = sigmaCore M ⊓ centralizer (X : Set G) :=
    inf_centralizer_sup_eq hdec hdecE hfree hXK hXbot
  have hAM : sigmaCore M ⊓ centralizer (X : Set G) ≤ M := (inf_le_left).trans (sigmaCore_le M)
  have h1 : (sigmaCore M ⊔ U).subgroupOf M ⊓ centralizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M)
      = (sigmaCore M ⊓ centralizer (X : Set G)).subgroupOf M := by
    ext x
    have hx := mem_centralizer_subgroupOf_iff hXM x
    constructor
    · intro hmem
      obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hmem
      refine (Subgroup.mem_subgroupOf).2 (hACeq ▸ ?_)
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_subgroupOf).1 hxD, hx.1 hxC⟩
    · intro hmem
      have h : (x : G) ∈ (sigmaCore M ⊔ U) ⊓ centralizer (X : Set G) :=
        hACeq ▸ (Subgroup.mem_subgroupOf).1 hmem
      obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 h
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_subgroupOf).2 hxD, hx.2 hxC⟩
  have h2 : K.subgroupOf M ⊓ normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M)
      = K.subgroupOf M := by
    refine inf_eq_left.2 fun x hx => ?_
    rw [mem_normalizer_subgroupOf_iff hXM]
    exact hKX ((Subgroup.mem_subgroupOf).1 hx)
  rw [h1, h2, ← Subgroup.subgroupOf_sup hAM hKM] at hform
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ (sup_le hAM hKM))
  · obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.1 hx
    have h : (⟨x, hxM⟩ : ↥M) ∈ normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
      (mem_normalizer_subgroupOf_iff hXM ⟨x, hxM⟩).2 hxN
    rw [hform] at h
    exact (Subgroup.mem_subgroupOf).1 h
  · exact sup_le ((inf_le_right).trans (Subgroup.centralizer_le_normalizer _)) hKX

theorem mem_tau13_of_mem_kappaPrimes [Fintype G] {M : Subgroup G} {p : ℕ}
    (hamb : IsAmbient G) (hM : IsCoatom M) (hp : p ∈ kappaPrimes M) :
    p ∈ tau1Primes M ∪ tau3Primes M := by
  obtain ⟨hpp, hpM, hpσ, S, hcyc, -⟩ := mem_kappaPrimes_iff.1 hp
  exact (CFSG.FeitThompson.mem_tau_union_and_mem_kappaPrimes_iff_of_isCyclic_sylow
    hamb.odd_natCard hamb.isSimpleGroup hamb.not_isMulCommutative hamb.forall_isSolvable hM hpp
    hpM hpσ ⟨S, hcyc⟩).1

theorem le_sigmaCore_of_natCard_prime [Finite G] {T X : Subgroup G} {p : ℕ}
    (hHall : CFSG.FeitThompson.IsHallPiSubgroupOf
      (sigmaPrimes T) (sigmaCore T) T)
    (hXT : X ≤ T) (hXp : Nat.card ↥X = p) (hp : p.Prime) (hpT : p ∈ sigmaPrimes T) :
    X ≤ sigmaCore T := by
  refine le_sigmaCore_of_isPiSubgroup hHall hXT (isPiSubgroup_iff.2 fun q hq => ?_)
  rw [hXp, hp.primeFactors, Finset.mem_singleton] at hq
  exact hq ▸ hpT

theorem FNI_kappa_normalizer_centralizer_structure
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonsigma_normalizer_reflected_plane.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_kappa_normalizer_centralizer_structure.{u} := by
  intro G _ _ M K A Z hsetup
  obtain ⟨hKbot, U, E₁, hUab, hUhall, hdec, hdecE, hE₁bot, hE₁hall, hE₁K,
    hnormX, hcentX, hcentK, hfree⟩ := h₃ G hsetup.ambient M K hsetup.isCoatom
      hsetup.kappa_nonempty hsetup.isHall_K
  have hamb := hsetup.ambient
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.forall_isSolvable⟩
  have hsolv : Group.IsSolvable ↥M := hamb.forall_isSolvable M hsetup.isCoatom.1
  have hcop := coprime_natCard_sigmaCore_sup hdec hdecE hUhall hsetup.isHall_K
  have hKM : K ≤ M := le_trans hdecE.2.1 hdec.2.1
  have hAeq : A = sigmaCore M ⊓ centralizer (K : Set G) := hsetup.A_eq
  have hgen : ∀ X : Subgroup G, X ≤ K → X ≠ ⊥ → K ≤ normalizer (X : Set G) →
      normalizer (X : Set G) ⊓ M = A ⊔ K := by
    intro X hXK hXbot hKX
    rw [normalizer_inf_eq_sup hsolv hdec hdecE hfree hcop hXK hXbot hKX, hAeq]
    congr 1
    exact hcentX X hXK hXbot
  have hKK : normalizer (K : Set G) ⊓ M = A ⊔ K :=
    hgen K le_rfl hKbot Subgroup.le_normalizer
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact le_inf Subgroup.le_normalizer hKM
  · rw [hKK]; exact le_sup_left
  · rw [hKK, sup_comm]
  ·
    rw [hAeq]
    have h1 : K ⊓ (sigmaCore M ⊓ centralizer (K : Set G)) ≤ K ⊓ sigmaCore M :=
      inf_le_inf_left _ inf_le_left
    refine le_bot_iff.1 (h1.trans ?_)
    rw [inf_comm]
    exact ((inf_le_inf_left _ (le_sup_right : K ≤ U ⊔ K)).trans hdec.2.2.2.2.le)
  ·
    have hAC : A ≤ centralizer (K : Set G) := hAeq ▸ inf_le_right
    have hc : ⁅A, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAC
    rw [Subgroup.commutator_comm]
    exact hc
  · intro X hXK hXbot hKX
    rw [hgen X hXK hXbot hKX, hKK]
  · intro X hXK hXp
    have hpp : (Nat.card ↥X).Prime := hXp
    have hXbot : X ≠ ⊥ := by
      intro h
      rw [h] at hXp
      simp only [Subgroup.card_bot] at hXp
      exact Nat.not_prime_one hXp
    refine ⟨hnormX X hXK hXp, by rw [hgen X hXK hXbot (hnormX X hXK hXp), hKK], ?_⟩
    intro T hT hNT
    have hpK : Nat.card ↥X ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hXK
    have hpκ : Nat.card ↥X ∈ kappaPrimes M :=
      hsetup.isHall_K.2.1 _ (Nat.mem_primeFactors.2 ⟨hpp, hpK, Nat.card_pos.ne'⟩)
    have hp13 := mem_tau13_of_mem_kappaPrimes hamb hsetup.isCoatom hpκ
    have hsc : CFSG.FeitThompson.Prep05.IsSigmaComplement M (U ⊔ K) :=
      ⟨hsetup.isCoatom, ⟨hdec.2.2.2.1, hdec.2.2.1, disjoint_iff.2 hdec.2.2.2.2⟩⟩
    have hXE : X ≤ U ⊔ K := hXK.trans le_sup_right
    have hCX : CFSG.FeitThompson.Prep05.centralizerIn
        (sigmaCore M) X ≠ ⊥ := by
      rw [CFSG.FeitThompson.Prep05.centralizerIn_eq]
      have hx := hcentX X hXK hXbot
      intro h
      exact hcentK (by rw [← hx]; exact h)
    have hpT : Nat.card ↥X ∈ sigmaPrimes T :=
      FNI_tau13_nonregular_line_normalizer_sigma h₁ h₂ h₄ h₅ h₆ h₇ h₈ h₉ G
        ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative,
          hamb.forall_isSolvable⟩ M (U ⊔ K) hsc _ hp13 X hXE rfl hCX T hT hNT
    exact le_sigmaCore_of_natCard_prime (h₁ G hG02 T hT).1
      (le_trans Subgroup.le_normalizer hNT) rfl hpp hpT

end

end CFSG.FeitThompson.Proofs
