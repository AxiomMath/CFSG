module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem geomSum_modEq_sub_one {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    (∑ i ∈ range n, p ^ i) ≡ n [MOD p - 1] := by
  have hp1 : p ≡ 1 [MOD p - 1] := ((Nat.modEq_iff_dvd' hp).mpr dvd_rfl).symm
  induction n with
  | zero => simp [Nat.ModEq.refl]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hpow : p ^ n ≡ 1 ^ n [MOD p - 1] := hp1.pow n
      simpa using ih.add hpow

theorem gcd_geomSum_sub_one {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    Nat.gcd (∑ i ∈ range q, p ^ i) (p - 1) = Nat.gcd q (p - 1) :=
  (geomSum_modEq_sub_one hp q).gcd_eq

theorem gcd_pow_sub_one_div_sub_one {p : ℕ} (hp : 2 ≤ p) (q : ℕ) :
    Nat.gcd ((p ^ q - 1) / (p - 1)) (p - 1) = Nat.gcd q (p - 1) := by
  rw [← Nat.geomSum_eq hp q]
  exact gcd_geomSum_sub_one (by omega) q

theorem coprime_pow_sub_one_div_sub_one_iff_not_dvd {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ↔ ¬ q ∣ (p - 1) := by
  rw [Nat.Coprime, gcd_pow_sub_one_div_sub_one hp q]
  exact hq.coprime_iff_not_dvd

theorem gcd_pow_sub_one_div_sub_one_eq_one_or_eq {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) :
    Nat.gcd ((p ^ q - 1) / (p - 1)) (p - 1) = 1 ∨
      Nat.gcd ((p ^ q - 1) / (p - 1)) (p - 1) = q := by
  rw [gcd_pow_sub_one_div_sub_one hp q]
  exact hq.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left q (p - 1))

end CFSG.FeitThompson
