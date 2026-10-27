module

public import CFSG.ClassicalInvolution.RouteD.TWYArith2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TWY

variable {p f q : ℕ}

theorem framesOdd_inj3 (hp : p.Prime) (hf : 1 ≤ f) (hqdef : q = p ^ f) (hq : 2 ≤ q) {j j' : ℕ}
    (h : framesOdd q j = framesOdd q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesOdd_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j) (framesOdd_unit hp hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesPlus_inj3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq : 2 ≤ q) {j j' : ℕ} (h : framesPlus q j = framesPlus q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesPlus_eq hqdef, framesPlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesPlus_unit hp hp2 hpq hq1 j)
    (framesPlus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesMinus_inj3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq : 2 ≤ q) {j j' : ℕ} (h : framesMinus q j = framesMinus q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesMinus_eq hqdef, framesMinus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesMinus_unit hp hp2 hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesOdd_ne_framesPlus3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq : 2 ≤ q) (j j' : ℕ) : framesOdd q j ≠ framesPlus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesPlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j)
    (framesPlus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesOdd_ne_framesMinus3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq : 2 ≤ q) (j j' : ℕ) : framesOdd q j ≠ framesMinus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesMinus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesPlus_ne_framesMinus3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq : 2 ≤ q) (j j' : ℕ) : framesPlus q j ≠ framesMinus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have h' := h
  rw [framesPlus_eq hqdef, framesMinus_eq hqdef] at h'
  have hx := pow_eq_of_mul_eq hp (framesPlus_unit hp hp2 hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h'
  have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  obtain rfl : j = j' + 1 := by omega
  exact absurd h (Nat.ne_of_gt (framesMinus_lt_framesPlus_succ hq j'))

end CFSG.ClassicalInvolution.Q3.Q3TIY
