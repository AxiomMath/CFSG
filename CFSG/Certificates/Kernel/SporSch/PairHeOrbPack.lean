module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.KS.SporSch.OrbCount

open Finset

theorem pack_lt (w : ℕ) (f : ℕ → ℕ) :
    ∀ L, (∀ m < L, f m < 2 ^ w) → ∑ i ∈ range L, f i * 2 ^ (w * i) < 2 ^ (w * L)
  | 0, _ => by simp
  | L + 1, hf => by
    rw [sum_range_succ]
    have h1 := pack_lt w f L fun m hm => hf m (by omega)
    have h2 : f L ≤ 2 ^ w - 1 := by have := hf L (by omega); omega
    have h3 : 2 ^ (w * (L + 1)) = 2 ^ (w * L) * 2 ^ w := by rw [Nat.mul_succ, pow_add]
    have h4 : 0 < 2 ^ w := Nat.two_pow_pos w
    calc ∑ i ∈ range L, f i * 2 ^ (w * i) + f L * 2 ^ (w * L)
        < 2 ^ (w * L) + (2 ^ w - 1) * 2 ^ (w * L) :=
          Nat.add_lt_add_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
      _ = 2 ^ (w * (L + 1)) := by
          rw [h3, Nat.sub_mul, one_mul, Nat.mul_comm (2 ^ w)]
          have : 2 ^ (w * L) ≤ 2 ^ (w * L) * 2 ^ w := Nat.le_mul_of_pos_right _ h4
          omega

theorem pack_digit (w : ℕ) (f : ℕ → ℕ) :
    ∀ L, (∀ m < L, f m < 2 ^ w) → ∀ m < L,
      (∑ i ∈ range L, f i * 2 ^ (w * i)) / 2 ^ (w * m) % 2 ^ w = f m
  | 0, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | L + 1, hf, m, hm => by
    rw [sum_range_succ]
    have hp : 0 < 2 ^ (w * m) := Nat.two_pow_pos _
    rcases Nat.lt_or_ge m L with h | h
    · have e : 2 ^ (w * L) = 2 ^ (w * m) * (2 ^ w * 2 ^ (w * (L - m - 1))) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have : m + 1 + (L - m - 1) = L := by omega
        calc w * L = w * (m + 1 + (L - m - 1)) := by rw [this]
          _ = w * m + (w + w * (L - m - 1)) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      rw [e, ← Nat.mul_assoc, Nat.mul_comm (f L), Nat.mul_assoc, Nat.add_mul_div_left _ _ hp,
        Nat.mul_left_comm, Nat.add_mul_mod_self_left]
      exact pack_digit w f L (fun i hi => hf i (by omega)) m h
    · have hmL : m = L := by omega
      subst hmL
      have h1 := pack_lt w f m fun i hi => hf i (by omega)
      rw [Nat.mul_comm (f m), Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, zero_add,
        Nat.mod_eq_of_lt (hf m (by omega))]

end CFSG.KS.SporSch.OrbCount

end
