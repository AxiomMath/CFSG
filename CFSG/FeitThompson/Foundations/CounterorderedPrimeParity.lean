module

import Mathlib.Data.Nat.Prime.Basic
import CFSG.FeitThompson.Foundations.PowerQuotientGcdCoprimality
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem two_dvd_sub_one_of_odd {p : ℕ} (hp : Odd p) : 2 ∣ p - 1 := by
  rcases hp with ⟨k, hk⟩
  omega

theorem ne_two_of_coprime_pow_sub_one_div_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) : q ≠ 2 := by
  have hq2 := hq.two_le
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnd := (coprime_pow_sub_one_div_sub_one_iff_not_dvd hp.two_le hq).mp hcop
  intro h
  exact hnd (h ▸ two_dvd_sub_one_of_odd hpodd)

theorem odd_of_coprime_pow_sub_one_div_sub_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) :
    5 ≤ p ∧ 3 ≤ q ∧ Odd p ∧ Odd q := by
  have hq2 := hq.two_le
  have hqne : q ≠ 2 := ne_two_of_coprime_pow_sub_one_div_sub_one hp hq hqp hcop
  have hqodd : Odd q := hq.odd_of_ne_two hqne
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [Nat.odd_iff] at hpodd hqodd
  refine ⟨by omega, by omega, ?_, ?_⟩ <;> rw [Nat.odd_iff] <;> omega

end CFSG.FeitThompson
