module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_mul_self (π : Perm α) : sign (π * π) = 1 := by
  rw [Perm.sign_mul]
  exact Int.units_mul_self _

theorem sign_involution {τ : Perm α} (hτ : τ * τ = 1) {k : ℕ} (hk : τ.support.card = 2 * k) :
    sign τ = (-1) ^ k := by
  have hc := cycleType_eq_replicate_of_involution hτ hk
  have h := Equiv.Perm.sign_of_cycleType τ
  rw [hc, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at h
  rw [h, pow_add, pow_mul, Int.units_pow_two, one_mul]

theorem even_of_sq_involution {π : Perm α} (hπ : (π * π) * (π * π) = 1) {k : ℕ}
    (hk : (π * π).support.card = 2 * k) : Even k := by
  have h := sign_involution hπ hk
  rw [sign_mul_self] at h
  have h2 : ((-1 : ℤˣ)) ^ k = 1 := h.symm
  exact (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).1 h2

end CFSG.OddStandard.Solomon75
