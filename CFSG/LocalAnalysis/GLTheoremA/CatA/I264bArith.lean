module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem not_sq_dvd_of_dvd_mul_squarefree {p S M N : ℕ} (hp : p.Prime) (hS : Nat.Coprime p S)
    (hM : Squarefree M) (hN : N ∣ S * M) : ¬ p ^ 2 ∣ N := by
  intro h
  have h1 : p ^ 2 ∣ S * M := h.trans hN
  have h2 : p ^ 2 ∣ M := (Nat.Coprime.pow_left 2 hS).dvd_of_dvd_mul_left h1
  have h3 : p * p ∣ M := by rwa [sq] at h2
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hM p h3))

theorem not_sq_dvd_of_dvd_smooth_mul {p a b M N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hM : Squarefree M) (hN : N ∣ 2 ^ a * 3 ^ b * M) : ¬ p ^ 2 ∣ N := by
  refine not_sq_dvd_of_dvd_mul_squarefree hp ?_ hM hN
  exact Nat.Coprime.mul_right
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3))

theorem squarefree_prime_mul {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) :
    Squarefree (a * b) :=
  (Nat.squarefree_mul ((Nat.coprime_primes ha hb).2 hab)).2 ⟨ha.squarefree, hb.squarefree⟩

theorem center_eq_bot_of_simple_nonprime {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {n : ℕ}
    (hS : Nat.card S = n) (hn : ¬ n.Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h1 | h1
  · exact h1
  · exfalso
    have hc : IsMulCommutative S := Subgroup.center_eq_top_iff.1 h1
    have hp := (@Group.is_simple_iff_prime_card S _ hc).1 inferInstance
    rw [hS] at hp
    exact hn hp

theorem exists_noncomm_of_simple_card {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {n : ℕ}
    (hS : Nat.card S = n) (hn : ¬ n.Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  have := IsSimpleGroup.prime_card (α := S)
  rw [hS] at this
  exact hn this

end CFSG.LocalAnalysis.GLTheoremA
