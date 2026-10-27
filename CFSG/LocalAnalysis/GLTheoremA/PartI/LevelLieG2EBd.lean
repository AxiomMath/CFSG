module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420 Finset

theorem pow_bound {a m k e g R ord : ℕ} (hm : Odd m) (hg : Nat.Coprime (2 ^ k) g)
    (hmul : g * ord = (2 ^ k) ^ e * R) (hd : ord ∣ 2 ^ a * m) : k * e ≤ a := by
  have h1 : (2 ^ k) ^ e ∣ g * ord := ⟨R, hmul⟩
  have h3 : (2 ^ k) ^ e ∣ g * (2 ^ a * m) := h1.trans (mul_dvd_mul_left g hd)
  have h4 : (2 ^ k) ^ e ∣ 2 ^ a * m := (Nat.Coprime.pow_left e hg).dvd_of_dvd_mul_left h3
  rw [← pow_mul] at h4
  by_contra h
  push Not at h
  have h5 : 2 ^ (a + 1) ∣ 2 ^ a * m := (pow_dvd_pow 2 h).trans h4
  rw [pow_succ] at h5
  have h6 : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h5
  exact hm.not_two_dvd_nat h6

theorem two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem orderA_bound {a m n k : ℕ} (hm : Odd m) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : orderA n (2 ^ k) ∣ 2 ^ a * m) : k * (n * (n + 1) / 2) ≤ a := by
  have hq2 := two_le_two_pow hk
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (2 ^ k - 1) ∣ (2 ^ k) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), ((2 ^ k) ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one (2 ^ k))).trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ k) ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (2 ^ k - 1) * orderA n (2 ^ k) = (2 ^ k) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), ((2 ^ k) ^ i - 1) := Nat.mul_div_cancel' hGd
  exact pow_bound hm (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h

theorem orderTwistedA_bound {a m n k : ℕ} (hm : Odd m) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : orderTwistedA n (2 ^ k) ∣ 2 ^ a * m) : k * (n * (n + 1) / 2) ≤ a := by
  have hq2 := two_le_two_pow hk
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : 2 ^ k + 1 ∣ (fun i => if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1) 2 := by
    show 2 ^ k + 1 ∣ (if Even 2 then (2 ^ k) ^ 2 - 1 else (2 ^ k) ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one (2 ^ k) (by omega)
  have hGd : Nat.gcd (n + 1) (2 ^ k + 1) ∣ (2 ^ k) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (2 ^ k + 1) * orderTwistedA n (2 ^ k) = (2 ^ k) ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then (2 ^ k) ^ i - 1 else (2 ^ k) ^ i + 1) :=
    Nat.mul_div_cancel' hGd
  exact pow_bound hm (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h

theorem orderBC_bound {a m n k : ℕ} (hm : Odd m) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : orderBC n (2 ^ k) ∣ 2 ^ a * m) : k * (n * n) ≤ a := by
  have hq2 := two_le_two_pow hk
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : 2 ^ k - 1 ∣ (fun i => (2 ^ k) ^ (2 * i) - 1) 1 := by
    show 2 ^ k - 1 ∣ (2 ^ k) ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ k) (2 * 1)
  have hGd : Nat.gcd 2 (2 ^ k - 1) ∣ (2 ^ k) ^ (n * n) * ∏ i ∈ Icc 1 n, ((2 ^ k) ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => (2 ^ k) ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (2 ^ k - 1) * orderBC n (2 ^ k) =
      (2 ^ k) ^ (n * n) * ∏ i ∈ Icc 1 n, ((2 ^ k) ^ (2 * i) - 1) := Nat.mul_div_cancel' hGd
  exact pow_bound hm (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h

theorem orderD_bound {a m n k : ℕ} (hm : Odd m) (hn : 4 ≤ n) (hk : 1 ≤ k)
    (h : orderD n (2 ^ k) ∣ 2 ^ a * m) : k * (n * (n - 1)) ≤ a := by
  have hq2 := two_le_two_pow hk
  have hGd : Nat.gcd 4 ((2 ^ k) ^ n - 1) ∣ (2 ^ k) ^ (n * (n - 1)) * (((2 ^ k) ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 ((2 ^ k) ^ n - 1) * orderD n (2 ^ k) = (2 ^ k) ^ (n * (n - 1)) *
      (((2 ^ k) ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) := by
    have h1 : (2 ^ k) ^ (n * (n - 1)) * ((2 ^ k) ^ n - 1) *
        ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1) = (2 ^ k) ^ (n * (n - 1)) *
        (((2 ^ k) ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) := by ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  exact pow_bound hm (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h

theorem orderTwistedD_bound {a m n k : ℕ} (hm : Odd m) (hn : 4 ≤ n) (hk : 1 ≤ k)
    (h : orderTwistedD n (2 ^ k) ∣ 2 ^ a * m) : k * (n * (n - 1)) ≤ a := by
  have hq2 := two_le_two_pow hk
  have hGd : Nat.gcd 4 ((2 ^ k) ^ n + 1) ∣ (2 ^ k) ^ (n * (n - 1)) * (((2 ^ k) ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 ((2 ^ k) ^ n + 1) * orderTwistedD n (2 ^ k) = (2 ^ k) ^ (n * (n - 1)) *
      (((2 ^ k) ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) := by
    have h1 : (2 ^ k) ^ (n * (n - 1)) * ((2 ^ k) ^ n + 1) *
        ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1) = (2 ^ k) ^ (n * (n - 1)) *
        (((2 ^ k) ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)) := by ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  exact pow_bound hm (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h


theorem orderE6_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderE6 (2 ^ k) ∣ 2 ^ a * m) : k * 36 ≤ a := by
  have hq2 := two_le_two_pow hk
  have hGd : Nat.gcd 3 ((2 ^ k) - 1) ∣ (2 ^ k) ^ 36 * ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 - 1) *
      ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 5 - 1) * ((2 ^ k) ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one (2 ^ k))) _
  have hmul : Nat.gcd 3 ((2 ^ k) - 1) * orderE6 (2 ^ k) = (2 ^ k) ^ 36 * (((2 ^ k) ^ 12 - 1) *
      ((2 ^ k) ^ 9 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 5 - 1) *
      ((2 ^ k) ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE6
    rw [show (2 ^ k) ^ 36 * (((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 - 1) * ((2 ^ k) ^ 8 - 1) *
      ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 5 - 1) * ((2 ^ k) ^ 2 - 1)) = (2 ^ k) ^ 36 *
      ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) *
      ((2 ^ k) ^ 5 - 1) * ((2 ^ k) ^ 2 - 1) by ring]
    exact this
  exact pow_bound hm (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h

theorem orderTwistedE6_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderTwistedE6 (2 ^ k) ∣ 2 ^ a * m) : k * 36 ≤ a := by
  have hq2 := two_le_two_pow hk
  have hGd : Nat.gcd 3 ((2 ^ k) + 1) ∣ (2 ^ k) ^ 36 * ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 + 1) *
      ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 5 + 1) * ((2 ^ k) ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (add_one_dvd_sq_sub_one (2 ^ k) (by omega))) _
  have hmul : Nat.gcd 3 ((2 ^ k) + 1) * orderTwistedE6 (2 ^ k) = (2 ^ k) ^ 36 *
      (((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 + 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) *
      ((2 ^ k) ^ 5 + 1) * ((2 ^ k) ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderTwistedE6
    rw [show (2 ^ k) ^ 36 * (((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 + 1) * ((2 ^ k) ^ 8 - 1) *
      ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 5 + 1) * ((2 ^ k) ^ 2 - 1)) = (2 ^ k) ^ 36 *
      ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 9 + 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) *
      ((2 ^ k) ^ 5 + 1) * ((2 ^ k) ^ 2 - 1) by ring]
    exact this
  exact pow_bound hm (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h

theorem orderE7_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderE7 (2 ^ k) ∣ 2 ^ a * m) : k * 63 ≤ a := by
  have hq2 := two_le_two_pow hk
  have hGd : Nat.gcd 2 ((2 ^ k) - 1) ∣ (2 ^ k) ^ 63 * ((2 ^ k) ^ 18 - 1) * ((2 ^ k) ^ 14 - 1) *
      ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 10 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) *
      ((2 ^ k) ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one (2 ^ k))) _
  have hmul : Nat.gcd 2 ((2 ^ k) - 1) * orderE7 (2 ^ k) = (2 ^ k) ^ 63 *
      (((2 ^ k) ^ 18 - 1) * ((2 ^ k) ^ 14 - 1) * ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 10 - 1) *
      ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE7
    rw [show (2 ^ k) ^ 63 * (((2 ^ k) ^ 18 - 1) * ((2 ^ k) ^ 14 - 1) * ((2 ^ k) ^ 12 - 1) *
      ((2 ^ k) ^ 10 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) =
      (2 ^ k) ^ 63 * ((2 ^ k) ^ 18 - 1) * ((2 ^ k) ^ 14 - 1) * ((2 ^ k) ^ 12 - 1) *
      ((2 ^ k) ^ 10 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1) by ring]
    exact this
  exact pow_bound hm (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h

theorem orderE8_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderE8 (2 ^ k) ∣ 2 ^ a * m) : k * 120 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 30 - 1) * ((2 ^ k) ^ 24 - 1) * ((2 ^ k) ^ 20 - 1) *
    ((2 ^ k) ^ 18 - 1) * ((2 ^ k) ^ 14 - 1) * ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 8 - 1) *
    ((2 ^ k) ^ 2 - 1)) hm (Nat.coprime_one_right _) (by unfold orderE8; ring) h

theorem orderF4_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderF4 (2 ^ k) ∣ 2 ^ a * m) : k * 24 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 12 - 1) * ((2 ^ k) ^ 8 - 1) * ((2 ^ k) ^ 6 - 1) *
    ((2 ^ k) ^ 2 - 1)) hm (Nat.coprime_one_right _) (by unfold orderF4; ring) h

theorem orderG2_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderG2 (2 ^ k) ∣ 2 ^ a * m) : k * 6 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) hm (Nat.coprime_one_right _)
    (by unfold orderG2; ring) h

theorem orderTrialityD4_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderTrialityD4 (2 ^ k) ∣ 2 ^ a * m) : k * 12 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) * ((2 ^ k) ^ 6 - 1) *
    ((2 ^ k) ^ 2 - 1)) hm (Nat.coprime_one_right _) (by unfold orderTrialityD4; ring) h

theorem orderSuzuki_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderSuzuki (2 ^ k) ∣ 2 ^ a * m) : k * 2 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 2 + 1) * (2 ^ k - 1)) hm (Nat.coprime_one_right _)
    (by unfold orderSuzuki; ring) h

theorem orderTwistedF4_bound {a m k : ℕ} (hm : Odd m) (hk : 1 ≤ k)
    (h : orderTwistedF4 (2 ^ k) ∣ 2 ^ a * m) : k * 12 ≤ a :=
  pow_bound (g := 1) (R := ((2 ^ k) ^ 6 + 1) * ((2 ^ k) ^ 4 - 1) * ((2 ^ k) ^ 3 + 1) *
    (2 ^ k - 1)) hm (Nat.coprime_one_right _) (by unfold orderTwistedF4; ring) h

end CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
