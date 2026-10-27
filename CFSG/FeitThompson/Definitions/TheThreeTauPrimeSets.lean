module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

theorem natCard_commutator_subtype (M : Subgroup G) :
    Nat.card (commutator M) = Nat.card (⁅M, M⁆ : Subgroup G) := by
  rw [← Subgroup.map_subtype_commutator, Subgroup.card_subtype]

def tau1Primes (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
    elementaryAbelianPRank p M = 1 ∧ ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G)}

theorem mem_tau1Primes_iff :
    p ∈ tau1Primes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := (Iff.rfl)

theorem mem_tau1Primes_iff_commutator :
    p ∈ tau1Primes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ ¬ p ∣ Nat.card (commutator M) := by
  rw [mem_tau1Primes_iff, natCard_commutator_subtype]

def tau3Primes (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
    elementaryAbelianPRank p M = 1 ∧ p ∣ Nat.card (⁅M, M⁆ : Subgroup G)}

theorem mem_tau3Primes_iff :
    p ∈ tau3Primes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := (Iff.rfl)

theorem mem_tau3Primes_iff_commutator :
    p ∈ tau3Primes M ↔ p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ p ∣ Nat.card (commutator M) := by
  rw [mem_tau3Primes_iff, natCard_commutator_subtype]

theorem prime_of_mem_tau1Primes (hp : p ∈ tau1Primes M) : p.Prime := hp.1

theorem prime_of_mem_tau3Primes (hp : p ∈ tau3Primes M) : p.Prime := hp.1

theorem dvd_natCard_of_mem_tau1Primes (hp : p ∈ tau1Primes M) : p ∣ Nat.card M := hp.2.1

theorem dvd_natCard_of_mem_tau3Primes (hp : p ∈ tau3Primes M) : p ∣ Nat.card M := hp.2.1

theorem notMem_sigmaPrimes_of_mem_tau1Primes (hp : p ∈ tau1Primes M) : p ∉ sigmaPrimes M := hp.2.2.1

theorem notMem_sigmaPrimes_of_mem_tau3Primes (hp : p ∈ tau3Primes M) : p ∉ sigmaPrimes M := hp.2.2.1

theorem elementaryAbelianPRank_eq_one_of_mem_tau1Primes (hp : p ∈ tau1Primes M) :
    elementaryAbelianPRank p M = 1 := hp.2.2.2.1

theorem elementaryAbelianPRank_eq_one_of_mem_tau3Primes (hp : p ∈ tau3Primes M) :
    elementaryAbelianPRank p M = 1 := hp.2.2.2.1

theorem not_dvd_natCard_commutator_of_mem_tau1Primes (hp : p ∈ tau1Primes M) :
    ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := hp.2.2.2.2

theorem dvd_natCard_commutator_of_mem_tau3Primes (hp : p ∈ tau3Primes M) :
    p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := hp.2.2.2.2

theorem tau1Primes_subset_setOf_prime (M : Subgroup G) : tau1Primes M ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

theorem tau3Primes_subset_setOf_prime (M : Subgroup G) : tau3Primes M ⊆ {p : ℕ | p.Prime} :=
  fun _ hp => hp.1

theorem disjoint_tau1Primes_sigmaPrimes (M : Subgroup G) :
    Disjoint (tau1Primes M) (sigmaPrimes M) :=
  Set.disjoint_left.2 fun _ h => notMem_sigmaPrimes_of_mem_tau1Primes h

theorem disjoint_tau3Primes_sigmaPrimes (M : Subgroup G) :
    Disjoint (tau3Primes M) (sigmaPrimes M) :=
  Set.disjoint_left.2 fun _ h => notMem_sigmaPrimes_of_mem_tau3Primes h

theorem disjoint_tau1Primes_tau3Primes (M : Subgroup G) :
    Disjoint (tau1Primes M) (tau3Primes M) :=
  Set.disjoint_left.2 fun _ h h' =>
    not_dvd_natCard_commutator_of_mem_tau1Primes h (dvd_natCard_commutator_of_mem_tau3Primes h')

theorem tau1Primes_union_tau3Primes (M : Subgroup G) :
    tau1Primes M ∪ tau3Primes M =
      {p | p.Prime ∧ p ∣ Nat.card M ∧ p ∉ sigmaPrimes M ∧ elementaryAbelianPRank p M = 1} := by
  ext p
  simp only [Set.mem_union, mem_tau1Primes_iff, mem_tau3Primes_iff, Set.mem_ofPred_eq]
  by_cases h : p ∣ Nat.card (⁅M, M⁆ : Subgroup G) <;> tauto

@[simp]
theorem tau1Primes_bot : tau1Primes (⊥ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_tau1Primes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hd
  rw [Subgroup.card_bot, Nat.dvd_one] at hd
  exact absurd hd hp.ne_one

@[simp]
theorem tau3Primes_bot : tau3Primes (⊥ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_tau3Primes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hd
  rw [Subgroup.card_bot, Nat.dvd_one] at hd
  exact absurd hd hp.ne_one

section Finite

variable [Finite G]

theorem mem_tau1Primes_iff' :
    p ∈ tau1Primes M ↔ p.Prime ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := by
  rw [mem_tau1Primes_iff]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun ⟨hp, h⟩ => ⟨hp, ?_, h⟩⟩
  exact (one_le_elementaryAbelianPRank_iff hp).1 h.2.1.ge

theorem mem_tau3Primes_iff' :
    p ∈ tau3Primes M ↔ p.Prime ∧ p ∉ sigmaPrimes M ∧
      elementaryAbelianPRank p M = 1 ∧ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) := by
  rw [mem_tau3Primes_iff]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun ⟨hp, h⟩ => ⟨hp, ?_, h⟩⟩
  exact (one_le_elementaryAbelianPRank_iff hp).1 h.2.1.ge

theorem tau1Primes_subset_primeFactors (M : Subgroup G) :
    tau1Primes M ⊆ ↑(Nat.card M).primeFactors := fun _ hp =>
  Nat.mem_primeFactors.2 ⟨hp.1, hp.2.1, Nat.card_pos.ne'⟩

theorem tau3Primes_subset_primeFactors (M : Subgroup G) :
    tau3Primes M ⊆ ↑(Nat.card M).primeFactors := fun _ hp =>
  Nat.mem_primeFactors.2 ⟨hp.1, hp.2.1, Nat.card_pos.ne'⟩

theorem tau1Primes_finite (M : Subgroup G) : (tau1Primes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset (tau1Primes_subset_primeFactors M)

theorem tau3Primes_finite (M : Subgroup G) : (tau3Primes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset (tau3Primes_subset_primeFactors M)

@[simp]
theorem tau1Primes_top : tau1Primes (⊤ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_tau1Primes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hd hσ
  rw [sigmaPrimes_top] at hσ
  exact absurd ⟨hp, by simpa using hd⟩ hσ

@[simp]
theorem tau3Primes_top : tau3Primes (⊤ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_tau3Primes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hd hσ
  rw [sigmaPrimes_top] at hσ
  exact absurd ⟨hp, by simpa using hd⟩ hσ

end Finite

end

end CFSG.FeitThompson
