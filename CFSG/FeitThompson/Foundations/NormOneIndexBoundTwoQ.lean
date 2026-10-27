module

public import CFSG.FeitThompson.Foundations.SmallKernelRatioForcesQThree
public import CFSG.FeitThompson.Foundations.QThreeQuadraticOrderThreshold
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p q : ℕ}

theorem sub_one_mul_cast_pow_sub_one_div_sub_one (hp : 2 ≤ p) (q : ℕ) :
    ((p : ℝ) - 1) * (((p ^ q - 1) / (p - 1) : ℕ) : ℝ) = (p : ℝ) ^ q - 1 := by
  rw [← Nat.geomSum_eq hp]
  push_cast
  rw [mul_comm, geom_sum_mul]

theorem pow_three_sub_one_div_sub_one (hp : 2 ≤ p) :
    (p ^ 3 - 1) / (p - 1) = p ^ 2 + p + 1 := by
  rw [← Nat.geomSum_eq hp]
  simp [Finset.sum_range_succ]
  ring

theorem sq_mod_six_eq_one (hp : p.Prime) (hp5 : 5 ≤ p) : p ^ 2 % 6 = 1 := by
  have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [Nat.pow_mod]
  rcases (by omega : p % 6 = 1 ∨ p % 6 = 5) with h | h <;> simp [h]

theorem sq_add_five_le_six_mul_of_sq_sub_one_div_six_lt (hp : p.Prime) (hp5 : 5 ≤ p) {u : ℕ}
    (hu : ((p : ℝ) ^ 2 - 1) / 6 < (u : ℝ)) : p ^ 2 + 5 ≤ 6 * u := by
  have hmod := sq_mod_six_eq_one hp hp5
  obtain ⟨k, hk⟩ : ∃ k, p ^ 2 = 6 * k + 1 := ⟨p ^ 2 / 6, by omega⟩
  have hcast : ((p : ℝ) ^ 2 - 1) / 6 = (k : ℝ) := by
    have h : ((p ^ 2 : ℕ) : ℝ) = 6 * (k : ℝ) + 1 := by rw [hk]; push_cast; ring
    push_cast at h
    linarith
  have hku : k < u := by exact_mod_cast hcast ▸ hu
  omega

theorem index_le_two_mul_of_kernelRatioCoeff_lt
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    {u b : ℕ} (hu0 : 0 < u) (hb0 : 0 < b)
    (hbu : b * u = (p ^ q - 1) / (p - 1))
    (hlt : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) / q < (u : ℝ)) :
    b ≤ 2 * q := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    have := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
    omega
  by_contra hcon
  have hb : 2 * q + 1 ≤ b := by omega
  have hPR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hQR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hM : 0 < kernelRatioCoeff p q := by
    have h := one_sub_lt_kernelRatioCoeff hp3 hq3
    have h1 : 1 / ((q : ℝ) - 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 1 / (q : ℝ) ^ 2 ≤ 1 / 9 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hX : (0 : ℝ) < (p : ℝ) ^ (q - 1) := by positivity
  have hB0 : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb0
  have hQ0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hBR : 2 * (q : ℝ) + 1 ≤ (b : ℝ) := by
    have h : ((2 * q + 1 : ℕ) : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hb
    push_cast at h
    linarith
  have hBUS : ((p : ℝ) - 1) * ((b : ℝ) * (u : ℝ)) = (p : ℝ) ^ q - 1 := by
    have h := sub_one_mul_cast_pow_sub_one_div_sub_one (p := p) hp.two_le q
    rw [← hbu] at h
    push_cast at h
    linarith
  have hu' : kernelRatioCoeff p q * (p : ℝ) ^ (q - 1) < (u : ℝ) * (q : ℝ) :=
    (div_lt_iff₀ hQ0).mp hlt
  have step1 : (2 * (q : ℝ) + 1) * (kernelRatioCoeff p q * (p : ℝ) ^ (q - 1))
      < (b : ℝ) * (u : ℝ) * (q : ℝ) := by
    calc (2 * (q : ℝ) + 1) * (kernelRatioCoeff p q * (p : ℝ) ^ (q - 1))
        ≤ (b : ℝ) * (kernelRatioCoeff p q * (p : ℝ) ^ (q - 1)) :=
          mul_le_mul_of_nonneg_right hBR (by positivity)
      _ < (b : ℝ) * ((u : ℝ) * (q : ℝ)) := mul_lt_mul_of_pos_left hu' hB0
      _ = (b : ℝ) * (u : ℝ) * (q : ℝ) := by ring
  have hPq : (p : ℝ) ^ q = (p : ℝ) * (p : ℝ) ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have step2 : ((2 * (q : ℝ) + 1) * kernelRatioCoeff p q * ((p : ℝ) - 1)) * (p : ℝ) ^ (q - 1)
      < ((q : ℝ) * (p : ℝ)) * (p : ℝ) ^ (q - 1) := by
    have h := mul_lt_mul_of_pos_left step1 (show (0 : ℝ) < (p : ℝ) - 1 by linarith)
    rw [show ((p : ℝ) - 1) * ((b : ℝ) * (u : ℝ) * (q : ℝ))
        = (((p : ℝ) - 1) * ((b : ℝ) * (u : ℝ))) * (q : ℝ) by ring, hBUS, hPq] at h
    nlinarith [h]
  have step3 : (2 * (q : ℝ) + 1) * kernelRatioCoeff p q * ((p : ℝ) - 1) < (q : ℝ) * (p : ℝ) :=
    lt_of_mul_lt_mul_right step2 hX.le
  have hd : (0 : ℝ) < (2 * (q : ℝ) + 1) * ((p : ℝ) - 1) := by nlinarith
  have hratio : kernelRatioCoeff p q
      < (q : ℝ) * (p : ℝ) / ((2 * (q : ℝ) + 1) * ((p : ℝ) - 1)) := by
    rw [lt_div_iff₀ hd]; nlinarith
  obtain ⟨hq3', hp5⟩ := eq_three_and_five_le_of_kernelRatioCoeff_lt hp hq hp2 hq2 hpq hratio
  subst hq3'
  rw [kernelRatioCoeff_three] at hlt
  norm_num at hlt
  have hint := sq_add_five_le_six_mul_of_sq_sub_one_div_six_lt hp hp5
    (sq_sub_one_div_six_lt_of_ratio_mul_sq_div_three_lt hp5 hlt)
  rw [pow_three_sub_one_div_sub_one hp.two_le] at hbu
  have hbu7 : 7 * u ≤ p ^ 2 + p + 1 :=
    hbu ▸ Nat.mul_le_mul_right u (by omega)
  nlinarith [hint, hbu7, hp5]

end CFSG.FeitThompson
