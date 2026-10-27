module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwoBasic
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.SeitzReduction.RankOne.LieTwo

open CFSG.Timmesfeld

theorem not_dvd_thirtySix {r : ℕ} (hr : r.Prime) (h3 : 3 < r) : ¬ r ∣ 36 := by
  have := not_dvd_prod_of_primes hr [2, 2, 3, 3] (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> exact ⟨by norm_num, by omega⟩)
  simpa using this

theorem not_dvd_sixtyThree {r : ℕ} (hr : r.Prime) (h7 : 7 < r) : ¬ r ∣ 63 := by
  have := not_dvd_prod_of_primes hr [3, 3, 7] (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl) <;> exact ⟨by norm_num, by omega⟩)
  simpa using this

theorem not_dvd_oneTwenty {r : ℕ} (hr : r.Prime) (h5 : 5 < r) : ¬ r ∣ 120 := by
  have := not_dvd_prod_of_primes hr [2, 2, 2, 3, 5] (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by norm_num, by omega⟩)
  simpa using this

theorem e6 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 5 - 1) * ((2 ^ f) ^ 2 - 1) = h * Nat.gcd 3 (2 ^ f - 1))
    (he : e = 36 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  refine false_of_ppd (f := f) (k := 5) (N := 36) (by omega) (by omega) (by rw [he, mul_comm])
    (by decide) (fun r hr => ?_) (fun r hr => not_dvd_thirtySix hr.prime ?_) hdiv
  · refine ppd_dvd_left hr (by omega) (g := Nat.gcd 3 (2 ^ f - 1)) (j := 1)
      (by rw [pow_one]; exact Nat.gcd_dvd_right _ _) (by decide) ?_
    rw [← hcof]
    exact ((ppd_dvd_pow_sub_one hr (a := 5) dvd_rfl).mul_left _).mul_right _
  · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    omega

theorem e7 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 18 - 1) * ((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 10 - 1) *
      ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) = h * Nat.gcd 2 (2 ^ f - 1))
    (he : e = 63 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  refine false_of_ppd (f := f) (k := 8) (N := 63) (by omega) (by omega) (by rw [he, mul_comm])
    (by decide) (fun r hr => ?_) (fun r hr => not_dvd_sixtyThree hr.prime ?_) hdiv
  · refine ppd_dvd_left hr (by omega) (g := Nat.gcd 2 (2 ^ f - 1)) (j := 1)
      (by rw [pow_one]; exact Nat.gcd_dvd_right _ _) (by decide) ?_
    rw [← hcof]
    exact (((ppd_dvd_pow_sub_one hr (a := 8) dvd_rfl).mul_left _).mul_right _).mul_right _
  · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    omega

theorem e8 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 30 - 1) * ((2 ^ f) ^ 24 - 1) * ((2 ^ f) ^ 20 - 1) * ((2 ^ f) ^ 18 - 1) *
      ((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 2 - 1) = h * 1)
    (he : e = 120 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  refine false_of_ppd (f := f) (k := 7) (N := 120) (by omega) (by omega) (by rw [he, mul_comm])
    (by decide) (fun r hr => ?_) (fun r hr => not_dvd_oneTwenty hr.prime ?_) hdiv
  · rw [← hcof]
    exact ((((ppd_dvd_pow_sub_one hr (a := 14) (by norm_num)).mul_left _).mul_right _).mul_right
      _).mul_right _
  · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    omega

theorem twistedE6 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) = h * Nat.gcd 3 (2 ^ f + 1))
    (he : e = 36 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  refine false_of_ppd (f := f) (k := 8) (N := 36) (by omega) (by omega) (by rw [he, mul_comm])
    (by decide) (fun r hr => ?_) (fun r hr => not_dvd_thirtySix hr.prime ?_) hdiv
  · refine ppd_dvd_left hr (by omega) (g := Nat.gcd 3 (2 ^ f + 1)) (j := 2)
      ((Nat.gcd_dvd_right _ _).trans (succ_dvd_sq_sub_one _))
      (by decide) ?_
    rw [← hcof]
    exact ((((ppd_dvd_pow_sub_one hr (a := 8) dvd_rfl).mul_left _).mul_right _).mul_right
      _).mul_right _
  · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    omega

theorem twistedB2 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1) = h * 1) (he : e = 2 * f)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  refine false_of_ppd (f := f) (k := 2 * 2) (N := 2) (by omega) (by omega)
    (by rw [he, mul_comm]) (by decide) (fun r hr => ?_) (fun r hr h2 => ?_) hdiv
  · rw [← hcof]
    exact (ppd_dvd_pow_add_one hr (by omega)).mul_right _
  · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    have := Nat.le_of_dvd two_pos h2
    omega

theorem g2 {f e h : ℕ} (hf : 2 ≤ f)
    (hcof : ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) = h * 1) (he : e = 6 * f)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  have h2e : 2 ^ e = (2 ^ f) ^ 6 := by rw [he, show 6 * f = f * 6 by ring, pow_mul]
  rw [h2e, ← hcof] at hdiv
  have hq : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have hX : 0 < (2 ^ f) ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left hX hdiv)
  have h8 : 4 * (2 * f) ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq (two_mul_le_two_pow f)
  rw [sq] at h1
  omega

theorem f4 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) =
      h * 1)
    (he : e = 24 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  have h64 : 2 ^ 6 * f ≤ (2 ^ f) ^ 6 := two_pow_mul_le_pow hf (by norm_num)
  set q := 2 ^ f with hq
  have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  have h24 : 1 ≤ q ^ 24 := Nat.one_le_pow _ _ (by omega)
  have h2e : 2 ^ e - 1 = (q ^ 12 - 1) * (q ^ 12 + 1) := by
    rw [he, show 24 * f = f * 24 by ring, pow_mul, ← hq]
    zify [h12, h24]
    ring
  have hX : 0 < q ^ 12 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hh : h = (q ^ 12 - 1) * ((q ^ 8 - 1) * (q ^ 2 - 1) * (q ^ 6 - 1)) := by
    rw [← hcof]; ring
  rw [h2e, hh, mul_assoc (q ^ 12 - 1) (q ^ 12 + 1) e] at hdiv
  have h1 := Nat.dvd_of_mul_dvd_mul_left hX hdiv
  have h2 : q ^ 6 - 1 ∣ (q ^ 12 + 1) * e := (dvd_mul_left _ _).trans h1
  have h3 : (q ^ 12 + 1) * e = (q ^ 6 - 1) * ((q ^ 6 + 1) * e) + 2 * e := by
    zify [h6]
    ring
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h2)
  norm_num at h64
  omega

theorem trialityD4 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1) = h * 1)
    (he : e = 12 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  have h64 : 2 ^ 6 * f ≤ (2 ^ f) ^ 6 := two_pow_mul_le_pow hf (by norm_num)
  have hodd : Odd ((2 ^ f) ^ 6 - 1) := odd_two_pow_pow_sub_one hf (by norm_num)
  set q := 2 ^ f with hq
  have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  have h2e : 2 ^ e - 1 = q ^ 12 - 1 := by rw [he, show 12 * f = f * 12 by ring, pow_mul]
  have hkey : h * (q ^ 2 + 1) = (q ^ 12 - 1) * (q ^ 6 - 1) := by
    rw [← hcof]
    zify [h2, h6, h12]
    ring
  have hX : 0 < q ^ 12 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  rw [h2e] at hdiv
  have h1 : (q ^ 12 - 1) * (q ^ 6 - 1) ∣ (q ^ 12 - 1) * ((q ^ 2 + 1) * e) := by
    rw [← hkey]
    calc h * (q ^ 2 + 1) ∣ (q ^ 12 - 1) * e * (q ^ 2 + 1) := Nat.mul_dvd_mul_right hdiv _
      _ = (q ^ 12 - 1) * ((q ^ 2 + 1) * e) := by ring
  have h3 := Nat.dvd_of_mul_dvd_mul_left hX h1
  have hcop : Nat.Coprime (q ^ 6 - 1) (q ^ 2 + 1) := by
    have hc1 : Nat.Coprime (q ^ 6 - 1) (q ^ 6 + 1) := by
      rw [show q ^ 6 + 1 = (q ^ 6 - 1) + 2 by omega, Nat.coprime_self_add_right]
      exact Nat.coprime_two_right.2 hodd
    have hd : q ^ 2 + 1 ∣ q ^ 6 + 1 := by
      have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      exact ⟨q ^ 4 - q ^ 2 + 1, by zify [h24]; ring⟩
    exact hc1.coprime_dvd_right hd
  have h5 := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_left h3)
  norm_num at h64
  omega

theorem twistedF4 {f e h : ℕ} (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ 6 + 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 3 + 1) * (2 ^ f - 1) = h * 1)
    (he : e = 12 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  have hcop : Nat.Coprime ((2 ^ f) ^ 2 + 1) (2 ^ f) :=
    Nat.Coprime.pow_right f
      (Nat.coprime_two_right.2 (odd_two_pow_pow_add_one hf (by norm_num)))
  have key : (2 ^ f) ^ 2 + 1 ∣ 12 * f := by
    rw [← he]
    set q := 2 ^ f with hq
    have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
    have h1' : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
    have h2e : 2 ^ e - 1 = (q ^ 6 + 1) * (q ^ 3 + 1) * (q - 1) * (q ^ 2 + q + 1) := by
      rw [he, show 12 * f = f * 12 by ring, pow_mul, ← hq]
      zify [h1', h12]
      ring
    have hh : h = (q ^ 6 + 1) * (q ^ 3 + 1) * (q - 1) * (q ^ 4 - 1) := by rw [← hcof]; ring
    have hP : 0 < (q ^ 6 + 1) * (q ^ 3 + 1) * (q - 1) :=
      Nat.mul_pos (by positivity) (by omega)
    rw [h2e, hh, mul_assoc ((q ^ 6 + 1) * (q ^ 3 + 1) * (q - 1))] at hdiv
    have hd1 := Nat.dvd_of_mul_dvd_mul_left hP hdiv
    have hd2 : q ^ 2 + 1 ∣ (q ^ 2 + q + 1) * e :=
      (Dvd.intro (q ^ 2 - 1) (by zify [h2, h4]; ring)).trans hd1
    have hd3 : q ^ 2 + 1 ∣ q * e := by
      rw [show (q ^ 2 + q + 1) * e = (q ^ 2 + 1) * e + q * e by ring] at hd2
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 hd2
    exact hcop.dvd_of_dvd_mul_left hd3
  rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | hf3
  · exact absurd key (by decide)
  · exact absurd key (by decide)
  · have hq8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
    have h16 : 8 * (2 * f) ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq8 (two_mul_le_two_pow f)
    have h5 := Nat.le_of_dvd (by omega) key
    rw [sq] at h5
    omega

theorem tits {e h : ℕ} (hcof : 8775 = h * 1) (he : e = 11 * 1)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  rw [mul_one] at hcof
  rw [he, ← hcof] at hdiv
  exact absurd hdiv (by decide)

end CFSG.SeitzReduction.RankOne.LieTwo
