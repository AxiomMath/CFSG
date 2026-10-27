module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

theorem exists_prime_ge_five_dvd_phi6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (h3 : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ≠ ℓ ∧
      (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
  set q : ℕ := ℓ ^ f with hq
  have hqodd : Odd q := (hℓ.odd_of_ne_two hℓ2).pow
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hℓ.pos
  have hmod : q % 3 = 2 := by
    have h3' : (3 : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 := by simpa [sub_eq_add_neg] using h3
    have h0 : (((q : ℤ) ^ 2 - q + 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast h3')
    push_cast at h0
    have key : ∀ x : ZMod 3, x ^ 2 - x + 1 = 0 → x = 2 := by decide
    have h2 := key _ h0
    have : ((q : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := by simpa using h2
    have := (ZMod.natCast_eq_natCast_iff' q 2 3).1 this
    omega
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    have : q = 2 := by omega
    rw [this] at hqodd
    exact absurd hqodd (by decide)
  set j := k * (k + 1) with hj
  have hjeven : Even j := Nat.even_mul_succ_self k
  set m : ℕ := 3 * j + 1 with hm
  have hm7 : 7 ≤ m := by
    have : 2 ≤ j := by
      have : 1 * 2 ≤ k * (k + 1) := Nat.mul_le_mul hk1 (by omega)
      omega
    omega
  have hmodd : Odd m := by
    obtain ⟨i, hi⟩ := hjeven
    exact ⟨3 * i, by omega⟩
  have hN : q ^ 2 - q + 1 = 3 * m := by
    have : q ^ 2 - q + 1 = (3 * k + 2) ^ 2 - (3 * k + 2) + 1 := by rw [hk]
    rw [this, hm, hj]
    have : (3 * k + 2) ^ 2 = 9 * k ^ 2 + 12 * k + 4 := by ring
    rw [this]
    have : 3 * (k * (k + 1)) = 3 * k ^ 2 + 3 * k := by ring
    omega
  have hmne : m ≠ 1 := by omega
  set r := m.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hmne
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hr2 : r ≠ 2 := by
    intro h
    rw [h] at hrm
    exact (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 hrm)
  have hr3 : r ≠ 3 := by
    intro h
    rw [h] at hrm
    omega
  have hr4 : r ≠ 4 := by
    intro h
    exact absurd (h ▸ hrp) (by decide)
  have hr5 : 5 ≤ r := by
    have := hrp.two_le
    omega
  refine ⟨r, hrp, hr5, ?_, ?_⟩
  · intro hrl
    have h1 : ℓ ∣ q ^ 2 - q + 1 := by
      rw [hN]; exact Dvd.dvd.mul_left (hrl ▸ hrm) 3
    have h2 : ℓ ∣ q := dvd_pow_self ℓ (by omega)
    have h3 : ℓ ∣ q ^ 2 - q := by
      have : q ^ 2 - q = q * (q - 1) := by
        rw [pow_two, Nat.mul_sub, mul_one]
      rw [this]; exact Dvd.dvd.mul_right h2 _
    have h4 : ℓ ∣ 1 := (Nat.dvd_add_right h3).1 h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)
  · have : (r : ℤ) ∣ ((3 * m : ℕ) : ℤ) := by exact_mod_cast Dvd.dvd.mul_left hrm 3
    have e : ((3 * m : ℕ) : ℤ) = (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1 := by
      have hle : q ≤ q ^ 2 := by nlinarith
      have : (((q ^ 2 - q + 1 : ℕ)) : ℤ) = (q : ℤ) ^ 2 - q + 1 := by
        push_cast [Nat.cast_sub hle]; ring
      rw [← hN, this]; ring
    rwa [e] at this

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
