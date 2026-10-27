module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
import CFSG.FeitThompson.OddOrder.SmallReversePowerPrimesThreeFive
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem pow_lt_sq_mul_cube_of_pred_div_le {p q : ℕ} (hq3 : 3 ≤ q) (hp3 : 3 ≤ p)
    (hle : ((q ^ p - 1) / (q - 1) - 1) / (p * q) ≤ p * q - 1) :
    q ^ p < p ^ 2 * q ^ 3 := by
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hle
  have hA : 0 < p * (c + 1) := Nat.mul_pos (by omega) (by omega)
  have hA1 : 1 < p * (c + 1) := by
    have := Nat.le_mul_of_pos_right p (show 0 < c + 1 by omega)
    omega
  have hAA : 1 < p * (c + 1) * (p * (c + 1)) := by
    have := Nat.le_mul_of_pos_right (p * (c + 1)) hA
    omega
  have hv : ((c + 1) ^ p - 1) / c * c = (c + 1) ^ p - 1 :=
    Nat.div_mul_cancel (by simpa using Nat.sub_one_dvd_pow_sub_one (x := c + 1) (n := p))
  have hqp1 : 1 < (c + 1) ^ p := Nat.one_lt_pow (by omega) (by omega)
  set v := ((c + 1) ^ p - 1) / c with hvdef
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h] at hv; omega
    · omega
  have hlt : v - 1 < p * (c + 1) * (p * (c + 1)) :=
    (Nat.div_lt_iff_lt_mul hA).mp (lt_of_le_of_lt hle (by omega))
  have h1 : (c + 1) ^ p - 1 ≤ p * (c + 1) * (p * (c + 1)) * c :=
    hv ▸ Nat.mul_le_mul_right _ (by omega)
  have h2 : p ^ 2 * (c + 1) ^ 3
      = p * (c + 1) * (p * (c + 1)) * c + p * (c + 1) * (p * (c + 1)) := by ring
  omega

theorem eq_three_and_eq_five_of_sub_one_div_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p)
    (hle : ((q ^ p - 1) / (q - 1) - 1) / (p * q) ≤ p * q - 1) :
    q = 3 ∧ p = 5 := by
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  refine eq_three_and_eq_five_of_pow_sub_three_lt_sq hp hq hpodd hqodd hqp ?_
  have hkey := pow_lt_sq_mul_cube_of_pred_div_le hq3 hp3 hle
  have hsplit : q ^ p = q ^ (p - 3) * q ^ 3 := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at hkey
  exact lt_of_mul_lt_mul_right hkey (Nat.zero_le _)

theorem eq_three_and_eq_five_of_sub_one_le_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p)
    (hle : (q ^ p - 1) / (q - 1) - 1 ≤ p * q * (p * q - 1)) :
    q = 3 ∧ p = 5 :=
  eq_three_and_eq_five_of_sub_one_div_le hp hq hpodd hqodd hqp (Nat.div_le_of_le_mul hle)

theorem eq_three_and_eq_five_of_geomSum_sub_one_div_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p)
    (hle : ((∑ i ∈ range p, q ^ i) - 1) / (p * q) ≤ p * q - 1) :
    q = 3 ∧ p = 5 := by
  have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
  refine eq_three_and_eq_five_of_sub_one_div_le hp hq hpodd hqodd hqp ?_
  rwa [← Nat.geomSum_eq (by omega)]

end CFSG.FeitThompson
