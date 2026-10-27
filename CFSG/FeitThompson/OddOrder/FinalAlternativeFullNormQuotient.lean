module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CFSG.FeitThompson.OddOrder.ReducedNormSupportKernelContradiction
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

variable {p q u h x : ℕ}

theorem mul_dvd_sub_one_of_modEq (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hh0 : 0 < h)
    (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) : p * q ∣ h - 1 :=
  ((Nat.coprime_primes hp hq).mpr hne).mul_dvd_of_dvd_of_dvd
    ((Nat.modEq_iff_dvd' hh0).mp hhp.symm) ((Nat.modEq_iff_dvd' hh0).mp hhq.symm)

theorem eq_geomSum_of_order_alternatives (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p)
    (hqodd : Odd q) (hqp : q < p) (hxodd : Odd x) (hh : h = u * x)
    (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q])
    (horder : u = ∑ i ∈ range q, p ^ i ∨ (p ≡ 1 [MOD q] ∧ q * u = ∑ i ∈ range q, p ^ i))
    (hbound : (h - 1) / (p * q) ≤ p * q - 1 ∨ (q = 3 ∧ p = 5)) :
    u = ∑ i ∈ range q, p ^ i := by
  obtain hu | ⟨hpq, hqu⟩ := horder
  · exact hu
  exfalso
  obtain hb | ⟨hq3, hp5⟩ := hbound
  swap
  · subst hq3; subst hp5; exact absurd hpq (by decide)
  have hpq0 : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hlt : h - 1 < p * q * (p * q) :=
    (Nat.div_lt_iff_lt_mul hpq0).mp (hb.trans_lt (by omega))
  have hsq : p ^ 2 * q ^ 2 = p * q * (p * q) := by ring
  exact not_geomSum_cofactor_le_sq hp hq hpodd hqodd hqp hpq hxodd hqu hh hhp hhq huq (by omega)

theorem eq_geomSum_of_order_alternatives' (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p)
    (hqodd : Odd q) (hqp : q < p) (_hu0 : 0 < u) (_hh0 : 0 < h) (_hx0 : 0 < x) (_huodd : Odd u)
    (_hhodd : Odd h) (hxodd : Odd x) (hh : h = u * x)
    (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q])
    (horder : u = ∑ i ∈ range q, p ^ i ∨ (p ≡ 1 [MOD q] ∧ q * u = ∑ i ∈ range q, p ^ i))
    (hbound : (h - 1) / (p * q) ≤ p * q - 1 ∨ (q = 3 ∧ p = 5)) :
    u = ∑ i ∈ range q, p ^ i :=
  eq_geomSum_of_order_alternatives hp hq hpodd hqodd hqp hxodd hh hhp hhq huq horder hbound

end CFSG.FeitThompson
