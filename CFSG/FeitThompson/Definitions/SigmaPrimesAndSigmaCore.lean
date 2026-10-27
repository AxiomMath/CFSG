module

public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

theorem map_subtype_map_conj (m : M) (Q : Subgroup M) :
    (Q.map (MulAut.conj m)).map M.subtype = (Q.map M.subtype).map (MulAut.conj (m : G)) := by
  rw [Subgroup.map_map, Subgroup.map_map]; congr 1

theorem normalizer_map_conj (P : Subgroup G) (g : G) :
    normalizer ((P.map (MulAut.conj g) : Subgroup G) : Set G)
      = (normalizer (P : Set G)).map (MulAut.conj g) :=
  (Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective).symm

theorem map_conj_eq_self {g : G} (hg : g ∈ M) : M.map (MulAut.conj g) = M :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)

def sigmaPrimes (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card M ∧
    ∃ S : Sylow p M, normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M}

theorem mem_sigmaPrimes_iff :
    p ∈ sigmaPrimes M ↔ p.Prime ∧ p ∣ Nat.card M ∧
      ∃ S : Sylow p M, normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M :=
  (Iff.rfl)

theorem prime_of_mem_sigmaPrimes (hp : p ∈ sigmaPrimes M) : p.Prime := hp.1

theorem dvd_natCard_of_mem_sigmaPrimes (hp : p ∈ sigmaPrimes M) : p ∣ Nat.card M := hp.2.1

theorem sigmaPrimes_subset_setOf_prime (M : Subgroup G) : sigmaPrimes M ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

theorem sigmaPrimes_subset_primeFactors [Finite G] (M : Subgroup G) :
    sigmaPrimes M ⊆ ↑(Nat.card M).primeFactors := fun _ hp =>
  Nat.mem_primeFactors.2 ⟨hp.1, hp.2.1, Nat.card_pos.ne'⟩

theorem sigmaPrimes_finite [Finite G] (M : Subgroup G) : (sigmaPrimes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset (sigmaPrimes_subset_primeFactors M)

theorem exists_sylow_map_subtype_eq_iff [Finite G] (hp : p.Prime) {P : Subgroup G} :
    (∃ S : Sylow p M, (S : Subgroup M).map M.subtype = P) ↔
      P ≤ M ∧ Nat.card P = p ^ (Nat.card M).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨Subgroup.map_subtype_le _, by rw [Subgroup.card_subtype]; exact S.card_eq_multiplicity⟩
  · rintro ⟨hPM, hcard⟩
    have hQ : Nat.card (P.subgroupOf M) = p ^ (Nat.card M).factorization p := by
      rw [← Subgroup.card_subtype M (P.subgroupOf M), Subgroup.map_subgroupOf_eq_of_le hPM]
      exact hcard
    exact ⟨Sylow.ofCard (P.subgroupOf M) hQ, by
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPM]⟩

theorem mem_sigmaPrimes_iff_exists_subgroup [Finite G] (hp : p.Prime) :
    p ∈ sigmaPrimes M ↔ p ∣ Nat.card M ∧ ∃ P : Subgroup G, P ≤ M ∧
      Nat.card P = p ^ (Nat.card M).factorization p ∧ normalizer (P : Set G) ≤ M := by
  rw [mem_sigmaPrimes_iff]
  simp only [hp, true_and]
  constructor
  · rintro ⟨hd, S, hS⟩
    obtain ⟨h1, h2⟩ := (exists_sylow_map_subtype_eq_iff hp).1 ⟨S, rfl⟩
    exact ⟨hd, _, h1, h2, hS⟩
  · rintro ⟨hd, P, h1, h2, h3⟩
    obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hp (P := P)).2 ⟨h1, h2⟩
    exact ⟨hd, S, by rw [hS]; exact h3⟩

theorem mem_sigmaPrimes_iff_forall [Finite G] (hp : p.Prime) :
    p ∈ sigmaPrimes M ↔ p ∣ Nat.card M ∧
      ∀ S : Sylow p M, normalizer (((S : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  rw [mem_sigmaPrimes_iff]
  simp only [hp, true_and]
  refine ⟨?_, fun h => ⟨h.1, (default : Sylow p M), h.2 _⟩⟩
  rintro ⟨hd, S, hS⟩
  refine ⟨hd, fun S' => ?_⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (M : Type _) S S'
  have h1 : (S : Subgroup M).map (MulAut.conj m) = (S' : Subgroup M) := by
    have h := Sylow.coe_subgroup_smul (g := m) (P := S)
    rw [hm] at h
    exact h.symm
  have h2 : ((S' : Subgroup M).map M.subtype : Subgroup G)
      = ((S : Subgroup M).map M.subtype).map (MulAut.conj (m : G)) := by
    rw [← h1, map_subtype_map_conj]
  rw [h2, normalizer_map_conj]
  exact (Subgroup.map_mono hS).trans (map_conj_eq_self m.2).le

theorem sigmaPrimes_top [Finite G] :
    sigmaPrimes (⊤ : Subgroup G) = {p | p.Prime ∧ p ∣ Nat.card G} := by
  ext p
  rw [mem_sigmaPrimes_iff]
  refine ⟨fun h => ⟨h.1, by simpa using h.2.1⟩, fun h => ⟨h.1, by simpa using h.2, ?_⟩⟩
  have : Fact p.Prime := ⟨h.1⟩
  exact ⟨(default : Sylow p (⊤ : Subgroup G)), le_top⟩

@[simp]
theorem sigmaPrimes_bot : sigmaPrimes (⊥ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_sigmaPrimes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hdvd
  rw [Subgroup.card_bot, Nat.dvd_one] at hdvd
  exact absurd hdvd hp.ne_one

def sigmaCore [Finite G] (M : Subgroup G) : Subgroup G :=
  (piCore (sigmaPrimes M) M).map M.subtype

variable [Finite G]

theorem sigmaCore_eq_map_piCore (M : Subgroup G) :
    sigmaCore M = (piCore (sigmaPrimes M) M).map M.subtype := (rfl)

theorem sigmaCore_le (M : Subgroup G) : sigmaCore M ≤ M := Subgroup.map_subtype_le _

theorem subgroupOf_sigmaCore (M : Subgroup G) :
    (sigmaCore M).subgroupOf M = piCore (sigmaPrimes M) M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

instance sigmaCore_normal_subgroupOf (M : Subgroup G) : ((sigmaCore M).subgroupOf M).Normal := by
  rw [subgroupOf_sigmaCore]; exact piCore_normal _ _

theorem le_normalizer_sigmaCore (M : Subgroup G) :
    M ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).1 (sigmaCore_normal_subgroupOf M)

theorem isPiSubgroup_sigmaCore (M : Subgroup G) : IsPiSubgroup (sigmaPrimes M) (sigmaCore M) :=
  isPiSubgroup_map_subtype_iff.2 (isPiSubgroup_piCore _ _)

theorem le_sigmaCore {N : Subgroup G} (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal)
    (hπ : IsPiSubgroup (sigmaPrimes M) N) : N ≤ sigmaCore M := by
  rw [sigmaCore_eq_map_piCore, le_map_piCore_iff _ hNM]
  exact le_piCore hN
    (isPiSubgroup_map_subtype_iff.1 (by rwa [Subgroup.map_subgroupOf_eq_of_le hNM]))

theorem isGreatest_sigmaCore (M : Subgroup G) :
    IsGreatest {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
      IsPiSubgroup (sigmaPrimes M) N} (sigmaCore M) :=
  ⟨⟨sigmaCore_le M, sigmaCore_normal_subgroupOf M, isPiSubgroup_sigmaCore M⟩,
    fun _ h => le_sigmaCore h.1 h.2.1 h.2.2⟩

@[simp]
theorem sigmaCore_bot : sigmaCore (⊥ : Subgroup G) = ⊥ :=
  le_bot_iff.1 ((sigmaCore_le _).trans le_rfl)

theorem sigmaCore_top : sigmaCore (⊤ : Subgroup G) = ⊤ := by
  have hpc : piCore (sigmaPrimes (⊤ : Subgroup G)) (⊤ : Subgroup G) = ⊤ := by
    refine eq_top_iff.2 (le_piCore (Subgroup.normal_of_characteristic ⊤)
      (isPiSubgroup_iff.2 fun q hq => ?_))
    rw [sigmaPrimes_top]
    have h1 : Nat.card (⊤ : Subgroup (⊤ : Subgroup G)) = Nat.card G := by simp
    rw [h1] at hq
    exact ⟨Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq⟩
  rw [sigmaCore_eq_map_piCore, hpc, map_top_subtype]

end

end CFSG.FeitThompson
