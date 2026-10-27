module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddFactor

public section

namespace CFSG.SeitzReduction.RankOne.LieOdd

theorem twoPartBound_pow_sub_one_of_eq {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (a b s u : ℕ)
    (hab : a = b + 1) (ha : a = 2 ^ s * u) (hu : Odd u) :
    TwoPartBound (q ^ a - 1) (q ^ b * (q - 1)) ((q + 1) * 2 ^ s) := by
  have h := twoPartBound_pow_sub_one hq hqodd ha hu
  rwa [show a - 1 = b by omega] at h

theorem twoPartBound_pow_add_one_of_eq {q : ℕ} (hq : 3 ≤ q) (hqodd : Odd q) (a b : ℕ)
    (hab : a = b + 1) : TwoPartBound (q ^ a + 1) (q ^ b * (q - 1)) (q + 1) := by
  have h := twoPartBound_pow_add_one hq hqodd (a := a) (by omega)
  rwa [show a - 1 = b by omega] at h

theorem twoPartBound_triality {q : ℕ} (hqodd : Odd q) :
    TwoPartBound (q ^ 8 + q ^ 4 + 1) (q ^ 8) 1 := by
  refine ⟨by omega, by omega, ?_⟩
  have hodd : Odd (q ^ 8 + q ^ 4 + 1) := (hqodd.pow.add_odd hqodd.pow).add_one
  exact (ordProj_two_of_odd hodd).le

theorem false_of_three_pow_mul_lt {q r M C : ℕ} (hq : 3 ≤ q) (hc : 3 ^ r * q ^ M < C)
    (hC : C ≤ 3 ^ r * 3 ^ M) : False := by
  have := Nat.mul_le_mul_left (3 ^ r) (Nat.pow_le_pow_left hq M)
  omega

theorem false_G2 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) = 2 ^ e * h * g) (hg : g ≤ 1)
    (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 6 - 1) * (q ^ 2 - 1)) (q ^ 6 * (q - 1) ^ 2)
      ((q + 1) ^ 2 * 2 ^ 2) := hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 9) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_F4 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 24 * ((q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 1) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := (((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
      (q ^ 24 * (q - 1) ^ 4) ((q + 1) ^ 4 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 43) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_E6 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 3) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := (((((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 9 8 0 9 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 5 4 0 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) (q ^ 36 * (q - 1) ^ 6) ((q + 1) ^ 6 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 65) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_E7 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 2) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := ((((((twoPartBound_pow_sub_one_of_eq hq hqodd 18 17 1 9 rfl rfl (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 14 13 1 7 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 10 9 1 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) (q ^ 63 * (q - 1) ^ 7) ((q + 1) ^ 7 * 2 ^ 10) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 118) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_E8 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 120 * ((q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
      (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 1) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := (((((((twoPartBound_pow_sub_one_of_eq hq hqodd 30 29 1 15 rfl rfl
      (by decide)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 24 23 3 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 20 19 2 5 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 18 17 1 9 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 14 13 1 7 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
      (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) (q ^ 120 * (q - 1) ^ 8)
      ((q + 1) ^ 8 * 2 ^ 14) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 231) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_twistedE6 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 3) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := (((((twoPartBound_pow_sub_one_of_eq hq hqodd 12 11 2 3 rfl rfl (by decide)).mul
    (twoPartBound_pow_add_one_of_eq hq hqodd 9 8 rfl)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 8 7 3 1 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_add_one_of_eq hq hqodd 5 4 rfl)).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) (q ^ 36 * (q - 1) ^ 6) ((q + 1) ^ 6 * 2 ^ 7) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 65) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_trialityD4 {q e h g : ℕ} (hq : 3 ≤ q) (hqodd : Odd q)
    (heq : q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 1) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hb := ((twoPartBound_triality hqodd).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 6 5 1 3 rfl rfl (by decide))).mul
    (twoPartBound_pow_sub_one_of_eq hq hqodd 2 1 1 1 rfl rfl (by decide))
  have hb' : TwoPartBound ((q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
      (q ^ 14 * (q - 1) ^ 2) ((q + 1) ^ 2 * 2 ^ 2) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq hqodd heq hb' hg he1 hdiv (M := 23) (by norm_num)
  exact false_of_three_pow_mul_lt hq hc (by norm_num)

theorem false_twistedG2 {q e h g : ℕ} (hq : 5 ≤ q) (hqodd : Odd q)
    (heq : q ^ 3 * ((q ^ 3 + 1) * (q - 1)) = 2 ^ e * h * g)
    (hg : g ≤ 1) (he1 : 1 ≤ e) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hq3 : 3 ≤ q := by omega
  have h1 := twoPartBound_pow_sub_one_of_eq hq3 hqodd 1 0 0 1 rfl rfl odd_one
  rw [pow_one] at h1
  have hb := (twoPartBound_pow_add_one_of_eq hq3 hqodd 3 2 rfl).mul h1
  have hb' : TwoPartBound ((q ^ 3 + 1) * (q - 1)) (q ^ 2 * (q - 1) ^ 2) ((q + 1) ^ 2 * 2 ^ 0) :=
    hb.mono (le_of_eq (by ring)) (le_of_eq (by ring))
  have hc := lt_of_twoPartBound hq3 hqodd heq hb' hg he1 hdiv (M := 2) (by norm_num)
  have := Nat.mul_le_mul_left (3 ^ 2) (Nat.pow_le_pow_left hq 2)
  norm_num at hc this
  omega

end CFSG.SeitzReduction.RankOne.LieOdd
