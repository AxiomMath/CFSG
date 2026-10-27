module

public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.SecondGeneration

theorem exists_mul_primeSupported_compl
    (π : Set ℕ) {n : ℕ} (hn : 0 < n) :
    ∃ a b : ℕ, n = a * b ∧ 0 < a ∧
      primeSupported π a ∧ primeSupported πᶜ b := by
  classical
  let f : ℕ → ℕ := fun p => p ^ n.factorization p
  let a := (n.primeFactors.filter (fun p => p ∈ π)).prod f
  let b := (n.primeFactors.filter (fun p => p ∈ πᶜ)).prod f
  have hsupp (ρ : Set ℕ) (s : Finset ℕ)
      (hs : ∀ p ∈ s, p ∈ n.primeFactors ∧ p ∈ ρ) :
      primeSupported ρ (s.prod f) := by
    intro q hq hqdvd
    obtain ⟨p, hp, hqp⟩ := hq.prime.exists_mem_finset_dvd hqdvd
    have hp' := hs p hp
    have hprime := Nat.prime_of_mem_primeFactors hp'.1
    have heq : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hqp)
    exact heq.symm ▸ hp'.2
  refine ⟨a, b, ?_, ?_,
    hsupp π _ (fun p hp => Finset.mem_filter.mp hp),
    hsupp πᶜ _ (fun p hp => Finset.mem_filter.mp hp)⟩
  · calc
      n = n.primeFactors.prod f := Nat.prod_primeFactors_pow_factorization hn.ne'
      _ = a * b :=
        (Finset.prod_filter_mul_prod_filter_not
          n.primeFactors (fun p => p ∈ π) f).symm
  · exact Finset.prod_pos fun p hp =>
      pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) _

theorem coprime_of_primeSupported_compl
    {π : Set ℕ} {a b : ℕ}
    (ha : primeSupported π a) (hb : primeSupported πᶜ b) :
    Nat.Coprime a b :=
  Nat.coprime_of_dvd fun p hp hpa hpb => hb p hp hpb (ha p hp hpa)

end CFSG.SecondGeneration
