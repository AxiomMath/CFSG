module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem two_dvd_of_pow_sub_one_of_pow_add_one {x m N A : ℕ} (hx : 1 ≤ x) (hm : Odd m)
    (h1 : A ∣ x ^ m - 1) (h2 : A ∣ x ^ N + 1) : A ∣ 2 := by
  have hx1 : 1 ≤ x ^ m := Nat.one_le_pow _ _ hx
  have e1 : ((x : ZMod A)) ^ m = 1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 h1
    push_cast [Nat.cast_sub hx1] at this
    exact sub_eq_zero.1 this
  have e2 : ((x : ZMod A)) ^ N = -1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 h2
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have e3 : (-1 : ZMod A) = 1 := by
    calc (-1 : ZMod A) = (-1) ^ m := hm.neg_one_pow.symm
      _ = ((x : ZMod A) ^ N) ^ m := by rw [e2]
      _ = ((x : ZMod A) ^ m) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [e1, one_pow]
  refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
  push_cast
  calc (2 : ZMod A) = 1 + 1 := by norm_num
    _ = 1 + (-1) := by rw [e3]
    _ = 0 := add_neg_cancel 1

theorem coprime_of_gcd_dvd_two {A f : ℕ} (hA : Odd A) (h : Nat.gcd A f ∣ 2) :
    Nat.Coprime A f := by
  have hg : Nat.gcd A f ∣ A := Nat.gcd_dvd_left A f
  have hodd : Odd (Nat.gcd A f) := hA.of_dvd_nat hg
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

section Core

variable {x m s : ℕ}

theorem coprime_pow_sub_one (hx : 1 ≤ x) (hm : 0 < m) (e : ℕ) :
    Nat.Coprime (x ^ m - 1) (x ^ e) := by
  refine Nat.Coprime.pow_right _ ?_
  have h1 : 1 ≤ x ^ m := Nat.one_le_pow _ _ hx
  have hxd : x ∣ x ^ m - 1 + 1 := by
    rw [Nat.sub_add_cancel h1]
    exact dvd_pow_self x hm.ne'
  have hc : Nat.Coprime (x ^ m - 1) (x ^ m - 1 + 1) := by simp
  exact Nat.Coprime.coprime_dvd_right hxd hc

theorem gcd_dvd_two (hx : 1 ≤ x) (hm : Odd m) (N : ℕ) :
    Nat.gcd (x ^ m - 1) (x ^ N + 1) ∣ 2 :=
  two_dvd_of_pow_sub_one_of_pow_add_one hx hm (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

theorem odd_pow_sub_one (hm : 0 < m) : Odd (2 ^ m - 1) := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨k, hk⟩ : 2 ∣ 2 ^ m := dvd_pow_self 2 hm.ne'
  exact Nat.odd_iff.2 (by omega)

theorem not_dvd_pow_sub_one (hx : 2 ≤ x) (_hm : 0 < m) (hns : ¬ m ∣ s)
    (h : x ^ m - 1 ∣ x ^ s - 1) : False := by
  have hg : Nat.gcd (x ^ m - 1) (x ^ s - 1) = x ^ Nat.gcd m s - 1 :=
    Nat.pow_sub_one_gcd_pow_sub_one x m s
  rw [Nat.gcd_eq_left h] at hg
  have h1 : 1 ≤ x ^ m := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ x ^ Nat.gcd m s := Nat.one_le_pow _ _ (by omega)
  have h3 : x ^ m = x ^ Nat.gcd m s := by omega
  have h4 := Nat.pow_right_injective hx h3
  apply hns
  rw [h4]
  exact Nat.gcd_dvd_right m s

theorem not_dvd_suzuki_order {m s : ℕ} (hm : Odd m) (hns : ¬ m ∣ s) :
    ¬ (2 ^ m - 1 ∣ (2 ^ s) ^ 2 * ((2 ^ s) ^ 2 + 1) * (2 ^ s - 1)) := by
  intro h
  have hm0 : 0 < m := hm.pos
  have hA := odd_pow_sub_one hm0
  have hc1 : Nat.Coprime (2 ^ m - 1) ((2 ^ s) ^ 2) :=
    Nat.Coprime.pow_right _ (coprime_pow_sub_one (by norm_num) hm0 s)
  rw [mul_assoc] at h
  have h1 := hc1.dvd_of_dvd_mul_left h
  have hc2 : Nat.Coprime (2 ^ m - 1) ((2 ^ s) ^ 2 + 1) := by
    refine coprime_of_gcd_dvd_two hA ?_
    have := gcd_dvd_two (x := 2) (by norm_num) hm (s * 2)
    rwa [pow_mul] at this
  exact not_dvd_pow_sub_one (x := 2) (by norm_num) hm0 hns (hc2.dvd_of_dvd_mul_left h1)

end Core

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
