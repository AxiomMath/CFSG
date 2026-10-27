module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CFSG.FeitThompson.OddOrder.ReducedNormBoundsPrimesThreeSeven
import CFSG.FeitThompson.OddOrder.SmallNormIndexLowerBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

variable {p q u h x : ℕ}

theorem not_geomSum_cofactor_le_sq (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hqp : q < p) (hpq : p ≡ 1 [MOD q]) (hxodd : Odd x)
    (hqu : q * u = ∑ i ∈ range q, p ^ i) (hh : h = u * x)
    (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q]) :
    ¬ h ≤ p ^ 2 * q ^ 2 := by
  intro hle
  have hq1 : 1 < q := hq.one_lt
  have hlt : p ^ q < h :=
    geomSum_lt_cofactor hpodd hqodd hq1 hqp hpq hxodd hqu hh hhp hhq huq
  obtain ⟨hq3, hp7⟩ :=
    eq_three_and_eq_seven_of_pow_lt hp hq hpodd hqodd hqp hpq (hlt.trans_le hle)
  subst hq3; subst hp7
  have hx : 3 + (3 + 1) * 7 ≤ x :=
    geomSum_index_lower_bound hpodd hqodd hq1 hqp hpq hxodd hqu hh hhp hhq huq
  have hsum : ∑ i ∈ range 3, 7 ^ i = 57 := by decide
  rw [hsum] at hqu
  have hu : u = 19 := by omega
  subst hu
  rw [hh] at hle
  omega

theorem not_exists_geomSum_cofactor_le_sq (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p)
    (hqodd : Odd q) (hqp : q < p) (hpq : p ≡ 1 [MOD q]) :
    ¬ ∃ u h x : ℕ, 0 < u ∧ 0 < h ∧ 0 < x ∧ Odd u ∧ Odd h ∧ Odd x ∧
      q * u = ∑ i ∈ range q, p ^ i ∧ h = u * x ∧ h ≡ 1 [MOD p] ∧ h ≡ 1 [MOD q] ∧
      u ≡ 1 [MOD q] ∧ h ≤ p ^ 2 * q ^ 2 := by
  rintro ⟨u, h, x, -, -, -, -, -, hxodd, hqu, hh, hhp, hhq, huq, hle⟩
  exact not_geomSum_cofactor_le_sq hp hq hpodd hqodd hqp hpq hxodd hqu hh hhp hhq huq hle

end CFSG.FeitThompson
