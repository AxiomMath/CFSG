module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Bound.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Ident

theorem n_le_e {n e : ℕ} (he : 1 ≤ e)
    (h : 2 ^ n ∣ ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 2 - 2 ^ e)) : n ≤ e := by
  have h2e : Even (2 ^ e) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have h2e' : Even ((2 ^ e) ^ 2) := (Nat.even_pow.mpr ⟨h2e, by norm_num⟩)
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hpos' : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ hpos
  have hu : Odd ((2 ^ e) ^ 2 - 1) := Nat.Even.sub_odd hpos' h2e' odd_one
  have hw : Odd (2 ^ e - 1) := Nat.Even.sub_odd hpos h2e odd_one
  have heq : ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 2 - 2 ^ e) =
      2 ^ e * (((2 ^ e) ^ 2 - 1) * (2 ^ e - 1)) := by
    have : (2 ^ e) ^ 2 - 2 ^ e = 2 ^ e * (2 ^ e - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [this]
    ring
  rw [heq] at h
  have hcop : Nat.Coprime (2 ^ n) (((2 ^ e) ^ 2 - 1) * (2 ^ e - 1)) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (hu.mul hw))
  have h3 := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3

theorem e_d_eq {n e d : ℕ} (hn : 1 ≤ n) (h : e * d = 2 * n) (hne : n ≤ e) (hd : 2 ≤ d) :
    d = 2 ∧ e = n := by
  have hd2 : d ≤ 2 := by
    by_contra hcon
    have h3 : 3 ≤ d := by omega
    nlinarith
  have hd' : d = 2 := by omega
  subst hd'
  omega

end CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
