module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M : Subgroup G}

def tauTwoPrimes (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∉ sigmaPrimes M ∧ elementaryAbelianPRank p M = 2}

theorem mem_tauTwoPrimes_iff :
    p ∈ tauTwoPrimes M ↔
      p.Prime ∧ p ∉ sigmaPrimes M ∧ elementaryAbelianPRank p M = 2 := (Iff.rfl)

theorem prime_of_mem_tauTwoPrimes (h : p ∈ tauTwoPrimes M) : p.Prime :=
  (mem_tauTwoPrimes_iff.1 h).1

theorem notMem_sigmaPrimes_of_mem_tauTwoPrimes (h : p ∈ tauTwoPrimes M) :
    p ∉ sigmaPrimes M := (mem_tauTwoPrimes_iff.1 h).2.1

theorem elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes (h : p ∈ tauTwoPrimes M) :
    elementaryAbelianPRank p M = 2 := (mem_tauTwoPrimes_iff.1 h).2.2

theorem tauTwoPrimes_subset_setOf_prime (M : Subgroup G) :
    tauTwoPrimes M ⊆ {p : ℕ | p.Prime} := fun _ h => prime_of_mem_tauTwoPrimes h

theorem tauTwoPrimes_disjoint_sigmaPrimes (M : Subgroup G) :
    Disjoint (tauTwoPrimes M) (sigmaPrimes M) :=
  Set.disjoint_left.2 fun _ h => notMem_sigmaPrimes_of_mem_tauTwoPrimes h

theorem sq_dvd_natCard_of_mem_tauTwoPrimes [Finite G] (h : p ∈ tauTwoPrimes M) :
    p ^ 2 ∣ Nat.card M := by
  simpa [elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h] using
    pow_elementaryAbelianPRank_dvd_card (X := (M : Type _)) (prime_of_mem_tauTwoPrimes h).one_lt

theorem dvd_natCard_of_mem_tauTwoPrimes [Finite G] (h : p ∈ tauTwoPrimes M) :
    p ∣ Nat.card M :=
  (dvd_pow_self p two_ne_zero).trans (sq_dvd_natCard_of_mem_tauTwoPrimes h)

theorem tauTwoPrimes_subset_primeFactors [Finite G] (M : Subgroup G) :
    tauTwoPrimes M ⊆ ↑(Nat.card M).primeFactors := fun _ h =>
  Nat.mem_primeFactors.2
    ⟨prime_of_mem_tauTwoPrimes h, dvd_natCard_of_mem_tauTwoPrimes h, Nat.card_pos.ne'⟩

theorem tauTwoPrimes_finite [Finite G] (M : Subgroup G) : (tauTwoPrimes M).Finite :=
  (Nat.card M).primeFactors.finite_toSet.subset (tauTwoPrimes_subset_primeFactors M)

theorem tauTwoPrimes_disjoint_alphaPrimes (M : Subgroup G) :
    Disjoint (tauTwoPrimes M) (alphaPrimes M) :=
  Set.disjoint_left.2 fun _ h h' => by
    have h3 := (mem_alphaPrimes.1 h').2
    rw [elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes h] at h3
    omega

theorem mem_tauTwoPrimes_iff_exists_subgroup [Finite G] :
    p ∈ tauTwoPrimes M ↔ p.Prime ∧ p ∉ sigmaPrimes M ∧
      (∃ H : Subgroup M, Nonempty (H ≃* (Fin 2 → Multiplicative (ZMod p)))) ∧
      ¬ ∃ H : Subgroup M, Nonempty (H ≃* (Fin 3 → Multiplicative (ZMod p))) := by
  rw [mem_tauTwoPrimes_iff]
  refine and_congr_right fun hp => and_congr_right fun _ => ?_
  rw [← mem_elementaryAbelianRanks (p := p) (d := 2) (X := (M : Type _)),
    ← mem_elementaryAbelianRanks (p := p) (d := 3) (X := (M : Type _)),
    ← le_elementaryAbelianPRank_iff hp.one_lt, ← le_elementaryAbelianPRank_iff hp.one_lt]
  omega

@[simp]
theorem tauTwoPrimes_bot : tauTwoPrimes (⊥ : Subgroup G) = ∅ := by
  ext p
  simp only [mem_tauTwoPrimes_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp _
  rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt]
  omega

end

end CFSG.FeitThompson
