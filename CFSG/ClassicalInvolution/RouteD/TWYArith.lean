module

public import CFSG.ClassicalInvolution.RouteD.TwinYR3Classify
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthArith

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f q : ℕ}

section Odd

theorem framesOdd_eq (hqdef : q = p ^ f) (j : ℕ) :
    framesOdd q j = ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1)) *
      p ^ (f * (4 * j + 4)) := by
  have e : p ^ (f * (4 * j + 4)) = q ^ (4 * j + 4) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold framesOdd
  ring

theorem framesOdd_unit (hp : p.Prime) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1) :=
  not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
    (pow_sub_one_coprime hp hpq hq1 (by omega))

theorem framesOdd_inj (hp : p.Prime) (hf : 1 ≤ f) (hqdef : q = p ^ f) (hq5 : 5 ≤ q) {j j' : ℕ}
    (h : framesOdd q j = framesOdd q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesOdd_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j) (framesOdd_unit hp hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end Odd

section Plus

theorem framesPlus_eq (hqdef : q = p ^ f) (j : ℕ) :
    framesPlus q j = ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) *
      ((q ^ (j + 1) - 1) * (q ^ j + 1))) * p ^ (f * (4 * j + 2)) := by
  have e : p ^ (f * (4 * j + 2)) = q ^ (4 * j + 2) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold framesPlus
  ring

theorem framesPlus_unit (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) * ((q ^ (j + 1) - 1) * (q ^ j + 1)) :=
  not_dvd_mul hp (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
    (pow_add_one_coprime hp hp2 hpq _))
    (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
      (pow_add_one_coprime hp hp2 hpq _))

theorem framesPlus_inj (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) {j j' : ℕ} (h : framesPlus q j = framesPlus q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesPlus_eq hqdef, framesPlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesPlus_unit hp hp2 hpq hq1 j)
    (framesPlus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end Plus

section Minus

theorem framesMinus_eq (hqdef : q = p ^ f) (j : ℕ) :
    framesMinus q j = ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1))) * p ^ (f * (4 * j + 6)) := by
  have e : p ^ (f * (4 * j + 6)) = q ^ (4 * j + 6) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold framesMinus
  ring

theorem framesMinus_unit (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) :=
  not_dvd_mul hp (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
    (pow_sub_one_coprime hp hpq hq1 (by omega)))
    (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
      (pow_sub_one_coprime hp hpq hq1 (by omega)))

theorem framesMinus_inj (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) {j j' : ℕ} (h : framesMinus q j = framesMinus q j') : j = j' := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesMinus_eq hqdef, framesMinus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesMinus_unit hp hp2 hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end Minus

section Cross

theorem framesOdd_ne_framesPlus (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) (j j' : ℕ) : framesOdd q j ≠ framesPlus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesPlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j)
    (framesPlus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framesOdd_ne_framesMinus (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) (j j' : ℕ) : framesOdd q j ≠ framesMinus q j' := by
  intro h
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framesOdd_eq hqdef, framesMinus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framesOdd_unit hp hpq hq1 j)
    (framesMinus_unit hp hp2 hpq hq1 j') h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end Cross

theorem pow_sub_one_ne_zero' {k : ℕ} (hq : 2 ≤ q) (hk : k ≠ 0) : q ^ k - 1 ≠ 0 := by
  have : 1 < q ^ k := Nat.one_lt_pow hk (by omega)
  omega

theorem framesOdd_ne_zero (hq : 2 ≤ q) (j : ℕ) : framesOdd q j ≠ 0 := by
  unfold framesOdd
  have hpos : 0 < q := by omega
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (pow_sub_one_ne_zero' hq (by omega))
    (pow_pos hpos _).ne') (Nat.mul_ne_zero (pow_sub_one_ne_zero' hq (by omega))
    (pow_pos hpos _).ne')



end CFSG.ClassicalInvolution.RouteD.TWY
