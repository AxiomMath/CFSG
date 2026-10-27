module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOrdNum
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open Finset
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem lieSOrd_orderA {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q)
    (hN : orderA n q ∈ lieSOrdN) : n = 1 ∧ q = 729 ∧ orderA n q = 193709880 := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq25, he⟩ := lieSOrd_gen_bound hq he1
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul hN
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ lieSOrdQ, orderA n q ∈ lieSOrdN →
      n = 1 ∧ q = 729 ∧ orderA n q = 193709880 := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid n (by simp; omega) q hq25 hN

theorem lieSOrd_orderTwistedA {n q : ℕ} (hn : 2 ≤ n) (hq : IsPrimePow q)
    (hN : orderTwistedA n q ∈ lieSOrdN) : False := by
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q + 1) * orderTwistedA n q = q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq25, he⟩ := lieSOrd_gen_bound hq he1
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul hN
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([2, 3, 4] : List ℕ), ∀ q ∈ lieSOrdQ, orderTwistedA n q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid n (by simp; omega) q hq25 hN

theorem lieSOrd_orderBC {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q)
    (hN : orderBC n q ∈ lieSOrdN) :
    (n = 3 ∧ q = 2 ∧ orderBC n q = 1451520) ∨ (n = 2 ∧ q = 8 ∧ orderBC n q = 1056706560) ∨
      (n = 1 ∧ q = 729 ∧ orderBC n q = 193709880) := by
  have hq2 := hq.two_le
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : q - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by
    show q - 1 ∣ q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one q (2 * 1)
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (q - 1) * orderBC n q = q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨hq25, he⟩ := lieSOrd_gen_bound hq he1
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul hN
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    nlinarith
  have grid : ∀ n ∈ ([1, 2, 3] : List ℕ), ∀ q ∈ lieSOrdQ, orderBC n q ∈ lieSOrdN →
      (n = 3 ∧ q = 2 ∧ orderBC n q = 1451520) ∨ (n = 2 ∧ q = 8 ∧ orderBC n q = 1056706560) ∨
        (n = 1 ∧ q = 729 ∧ orderBC n q = 193709880) := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid n (by simp; omega) q hq25 hN

theorem lieSOrd_orderD {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q)
    (hN : orderD n q ∈ lieSOrdN) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n - 1) ∣ q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n - 1) * orderD n q = q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hq25, he⟩ := lieSOrd_gen_bound hq he1
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul hN
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ lieSOrdQ, orderD 4 q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq25 hN

theorem lieSOrd_orderTwistedD {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q)
    (hN : orderTwistedD n q ∈ lieSOrdN) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n + 1) ∣ q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n + 1) * orderTwistedD n q = q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hq25, he⟩ := lieSOrd_gen_bound hq he1
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul hN
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ lieSOrdQ, orderTwistedD 4 q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq25 hN

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
