module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

theorem l3u3_suN_padicValNat_two {N n A B : ℕ} (hA : Odd A) (hB : Odd B)
    (hN : 3 * N = 2 ^ (3 * n) * (A * B)) : padicValNat 2 N = 3 * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAB : A * B ≠ 0 := mul_ne_zero hA.pos.ne' hB.pos.ne'
  have hN0 : N ≠ 0 := by
    intro h0
    have h1 : 2 ^ (3 * n) * (A * B) = 0 := by rw [← hN, h0]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hAB h1
  have hv := congrArg (padicValNat 2) hN
  rw [padicValNat.mul (by norm_num) hN0, padicValNat.mul (pow_ne_zero _ (by norm_num)) hAB,
    padicValNat.mul hA.pos.ne' hB.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hA)),
    padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hB))] at hv
  omega

theorem l3u3_suN_size_L {N n : ℕ} (hn : 2 ≤ n)
    (hN : 3 * N = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1))) :
    2 ^ (8 * n) ≤ 4 * N := by
  have hx : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have e2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  have e3 : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm, pow_mul]
  have e8 : 2 ^ (8 * n) = (2 ^ n) ^ 8 := by rw [mul_comm, pow_mul]
  rw [e2, e3] at hN
  rw [e8]
  generalize 2 ^ n = x at hx hN ⊢
  obtain ⟨a, ha⟩ : ∃ a, x ^ 2 = a + 1 :=
    ⟨x ^ 2 - 1, by have := Nat.one_le_pow 2 x (by omega); omega⟩
  obtain ⟨b, hb⟩ : ∃ b, x ^ 3 = b + 1 :=
    ⟨x ^ 3 - 1, by have := Nat.one_le_pow 3 x (by omega); omega⟩
  have ha' : x ^ 2 - 1 = a := by omega
  have hb' : x ^ 3 - 1 = b := by omega
  rw [ha', hb'] at hN
  have hx2 : 16 ≤ x ^ 2 := by nlinarith
  have hx3 : 4 * x ^ 2 ≤ x ^ 3 := calc
    4 * x ^ 2 ≤ x * x ^ 2 := Nat.mul_le_mul_right _ hx
    _ = x ^ 3 := by ring
  have ha15 : 15 ≤ a := by omega
  have hb4 : 4 * a + 3 ≤ b := by omega
  have h5 : x ^ 5 = (a + 1) * (b + 1) := by rw [← ha, ← hb]; ring
  have key : 3 * ((a + 1) * (b + 1)) ≤ 4 * (a * b) := by nlinarith
  have h8 : x ^ 8 = x ^ 3 * ((a + 1) * (b + 1)) := by rw [← h5]; ring
  have h1 : 3 * x ^ 8 ≤ 3 * (4 * N) := by
    calc 3 * x ^ 8 = x ^ 3 * (3 * ((a + 1) * (b + 1))) := by rw [h8]; ring
      _ ≤ x ^ 3 * (4 * (a * b)) := Nat.mul_le_mul_left _ key
      _ = 4 * (3 * N) := by rw [hN]; ring
      _ = 3 * (4 * N) := by ring
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem l3u3_suN_size_U {N n : ℕ} (hn : 2 ≤ n)
    (hN : 3 * N = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) :
    2 ^ (8 * n) ≤ 4 * N := by
  have hx : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have e2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm, pow_mul]
  have e3 : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm, pow_mul]
  have e8 : 2 ^ (8 * n) = (2 ^ n) ^ 8 := by rw [mul_comm, pow_mul]
  rw [e2, e3] at hN
  rw [e8]
  generalize 2 ^ n = x at hx hN ⊢
  obtain ⟨a, ha⟩ : ∃ a, x ^ 2 = a + 1 :=
    ⟨x ^ 2 - 1, by have := Nat.one_le_pow 2 x (by omega); omega⟩
  have ha' : x ^ 2 - 1 = a := by omega
  rw [ha'] at hN
  have hx2 : 16 ≤ x ^ 2 := by nlinarith
  have ha15 : 15 ≤ a := by omega
  have hx3 : 0 ≤ x ^ 3 := Nat.zero_le _
  have h5 : x ^ 5 = (a + 1) * x ^ 3 := by rw [← ha]; ring
  have key : 3 * ((a + 1) * x ^ 3) ≤ 4 * (a * (x ^ 3 + 1)) := by nlinarith
  have h8 : x ^ 8 = x ^ 3 * ((a + 1) * x ^ 3) := by rw [← h5]; ring
  have h1 : 3 * x ^ 8 ≤ 3 * (4 * N) := by
    calc 3 * x ^ 8 = x ^ 3 * (3 * ((a + 1) * x ^ 3)) := by rw [h8]; ring
      _ ≤ x ^ 3 * (4 * (a * (x ^ 3 + 1))) := Nat.mul_le_mul_left _ key
      _ = 4 * (3 * N) := by rw [hN]; ring
      _ = 3 * (4 * N) := by ring
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem l3u3_suN_param {N : ℕ} (h : L3U3Order N) :
    ∃ n : ℕ, 2 ≤ n ∧ ¬ 3 ∣ n ∧ padicValNat 2 N = 3 * n ∧ 2 ^ (8 * n) ≤ 4 * N := by
  obtain ⟨n, ⟨hn6, hN⟩ | ⟨hn6, hn1, hN⟩⟩ := h
  · have hn : n ≠ 0 := by omega
    refine ⟨n, by omega, by omega, l3u3_suN_padicValNat_two ?_ ?_ hN,
      l3u3_suN_size_L (by omega) hN⟩
    · rw [two_pow_two_mul]
      exact odd_four_pow_sub_one hn
    · rw [two_pow_three_mul]
      exact odd_eight_pow_sub_one hn
  · have hn : n ≠ 0 := by omega
    refine ⟨n, by omega, by omega, l3u3_suN_padicValNat_two ?_ ?_ hN,
      l3u3_suN_size_U (by omega) hN⟩
    · rw [two_pow_two_mul]
      exact odd_four_pow_sub_one hn
    · rw [two_pow_three_mul]
      exact odd_eight_pow_add_one hn

theorem l3u3_suN_prod_Icc_two_three (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 3, (Q ^ i - (-1) ^ i) = (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  have e : Finset.Icc 2 3 = {2, 3} := by decide
  rw [e]
  simp

theorem l3u3_suN_factor_pos {Q : ℤ} (hQ : 2 ≤ Q) {i : ℕ} (hi : 1 ≤ i) :
    0 < Q ^ i - (-1) ^ i := by
  have h1 : 2 ≤ Q ^ i := calc
    2 ≤ Q := hQ
    _ = Q ^ 1 := (pow_one Q).symm
    _ ≤ Q ^ i := pow_le_pow_right₀ (by omega) hi
  rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> omega

theorem l3u3_suN_prod_pos {Q : ℤ} (hQ : 2 ≤ Q) (ν : ℕ) :
    0 < ∏ i ∈ Finset.Icc 2 ν, (Q ^ i - (-1) ^ i) :=
  Finset.prod_pos fun i hi =>
    l3u3_suN_factor_pos hQ (by have := (Finset.mem_Icc.1 hi).1; omega)

theorem l3u3_suN_prod_odd {Q : ℤ} (hQe : Even Q) (ν : ℕ) :
    Odd (∏ i ∈ Finset.Icc 2 ν, (Q ^ i - (-1) ^ i)) := by
  refine Finset.prod_induction _ (fun x : ℤ => Odd x) (fun a b ha hb => ha.mul hb) odd_one ?_
  intro i hi
  have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
  have h1 : Even (Q ^ i) := hQe.pow_of_ne_zero hi1
  have h2 : Odd ((-1 : ℤ) ^ i) := by
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h]
    · exact odd_one
    · exact odd_neg_one
  exact h1.sub_odd h2

theorem l3u3_suN_sum_Icc {ν : ℕ} (hν : 1 ≤ ν) :
    2 * (∑ i ∈ Finset.Icc 2 ν, i) + 2 = ν * (ν + 1) := by
  induction ν, hν using Nat.le_induction with
  | base => decide
  | succ ν hν ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith

theorem l3u3_suN_prod_bound {Q : ℤ} (hQ : 2 ≤ Q) {ν : ℕ} (hν : 1 ≤ ν) :
    2 ^ ν * ∏ i ∈ Finset.Icc 2 ν, (Q ^ i + 1) + 2 * Q ^ (∑ i ∈ Finset.Icc 2 ν, i) ≤
      2 ^ (ν + 1) * Q ^ (∑ i ∈ Finset.Icc 2 ν, i) := by
  induction ν, hν using Nat.le_induction with
  | base =>
    have e : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
    rw [e]
    norm_num
  | succ ν hν ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      pow_add Q (∑ i ∈ Finset.Icc 2 ν, i) (ν + 1)]
    have hA : 0 ≤ Q ^ (∑ i ∈ Finset.Icc 2 ν, i) := by positivity
    have hq : 2 ^ (ν + 1) ≤ Q ^ (ν + 1) := pow_le_pow_left₀ (by norm_num) hQ _
    have h2 : (2 : ℤ) ^ (ν + 1) = 2 * 2 ^ ν := by ring
    have h4 : (2 : ℤ) ^ (ν + 1 + 1) = 4 * 2 ^ ν := by ring
    have ht : (0 : ℤ) < 2 ^ ν := by positivity
    rw [h2] at hq ih ⊢
    rw [h4]
    generalize Q ^ (∑ i ∈ Finset.Icc 2 ν, i) = A at hA ih ⊢
    generalize ∏ i ∈ Finset.Icc 2 ν, (Q ^ i + 1) = P at ih ⊢
    generalize Q ^ (ν + 1) = q at hq ⊢
    generalize (2 : ℤ) ^ ν = t at hq ih ht ⊢
    have hq0 : 0 ≤ q + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right ih hq0, mul_nonneg hA (sub_nonneg.2 hq)]

theorem l3u3_suN_prod_lt {Q : ℤ} (hQ : 2 ≤ Q) {ν : ℕ} (hν : 1 ≤ ν) :
    ∏ i ∈ Finset.Icc 2 ν, (Q ^ i - (-1) ^ i) < 2 * Q ^ (∑ i ∈ Finset.Icc 2 ν, i) := by
  have hle : ∏ i ∈ Finset.Icc 2 ν, (Q ^ i - (-1) ^ i) ≤ ∏ i ∈ Finset.Icc 2 ν, (Q ^ i + 1) := by
    refine Finset.prod_le_prod₀ (fun i hi => (l3u3_suN_factor_pos hQ ?_).le) fun i _ => ?_
    · have := (Finset.mem_Icc.1 hi).1
      omega
    · rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> omega
  have hb := l3u3_suN_prod_bound hQ hν
  have hA : 0 < Q ^ (∑ i ∈ Finset.Icc 2 ν, i) := by positivity
  have h2 : (0 : ℤ) < 2 ^ ν := by positivity
  by_contra hcon
  push Not at hcon
  rw [pow_succ] at hb
  nlinarith [mul_le_mul_of_nonneg_left hcon h2.le, mul_le_mul_of_nonneg_left hle h2.le]

theorem l3u3_suN_ge_five_arith {ν N z m : ℕ} (hν : 5 ≤ ν) (hN : L3U3Order N) (hm : 1 ≤ m)
    (hz : Odd z)
    (hcard : ((N * z : ℕ) : ℤ) = ((2 ^ m : ℕ) : ℤ) ^ (ν * (ν - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 ν, (((2 ^ m : ℕ) : ℤ) ^ i - (-1) ^ i)) : False := by
  obtain ⟨n, hn2, -, hv2, hsize⟩ := l3u3_suN_param hN
  obtain ⟨k, rfl⟩ : ∃ k, ν = k + 5 := ⟨ν - 5, by omega⟩
  set T := (k + 5) * (k + 5 - 1) / 2 with hTdef
  set S := ∑ i ∈ Finset.Icc 2 (k + 5), i with hSdef
  have hT : 2 * T = (k + 5) * (k + 5 - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self (k + 5)))
  have hS : 2 * S + 2 = (k + 5) * (k + 5 + 1) := l3u3_suN_sum_Icc (by omega)
  have hk4 : k + 5 - 1 = k + 4 := by omega
  rw [hk4] at hT
  have hTS : 3 * S + 8 ≤ 5 * T := by nlinarith
  have hQ2 : (2 : ℤ) ≤ 2 ^ m := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hQe : Even ((2 : ℤ) ^ m) := (Nat.even_pow.2 ⟨by decide, by omega⟩ : Even (2 ^ m)).natCast
  have hcast : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by push_cast; rfl
  rw [hcast] at hcard
  have hFpos := l3u3_suN_prod_pos hQ2 (k + 5)
  have hFodd := l3u3_suN_prod_odd hQe (k + 5)
  have hFlt := l3u3_suN_prod_lt hQ2 (show 1 ≤ k + 5 by omega)
  obtain ⟨Fn, hFn⟩ : ∃ Fn : ℕ,
      (Fn : ℤ) = ∏ i ∈ Finset.Icc 2 (k + 5), (((2 : ℤ) ^ m) ^ i - (-1) ^ i) :=
    ⟨_, Int.toNat_of_nonneg hFpos.le⟩
  rw [← hFn] at hcard hFodd hFlt hFpos
  have hnat : N * z = (2 ^ m) ^ T * Fn := by exact_mod_cast hcard
  have hFnodd : Odd Fn := by
    have := Int.odd_iff.1 hFodd
    exact Nat.odd_iff.2 (by omega)
  have hFnlt : Fn < 2 * (2 ^ m) ^ S := by exact_mod_cast hFlt
  have hFn0 : Fn ≠ 0 := hFnodd.pos.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz0 : z ≠ 0 := hz.pos.ne'
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hv2
    simp at hv2
    omega
  have hv : padicValNat 2 (N * z) = m * T := by
    rw [hnat, padicValNat.mul (pow_ne_zero _ (by norm_num)) hFn0, ← pow_mul,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2
        (Nat.odd_iff.1 hFnodd)), add_zero]
  rw [padicValNat.mul hN0 hz0, hv2, padicValNat.eq_zero_of_not_dvd
    (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hz)), add_zero] at hv
  have hle1 : N ≤ N * z := Nat.le_mul_of_pos_right N hz.pos
  have hlt : N * z < 2 * 2 ^ (m * (T + S)) := by
    rw [hnat]
    calc (2 ^ m) ^ T * Fn < (2 ^ m) ^ T * (2 * (2 ^ m) ^ S) :=
          Nat.mul_lt_mul_of_pos_left hFnlt (by positivity)
      _ = 2 * 2 ^ (m * (T + S)) := by rw [mul_add, pow_add, ← pow_mul, ← pow_mul]; ring
  have h8 : 2 ^ (8 * n) < 2 ^ (m * (T + S) + 3) := by
    calc 2 ^ (8 * n) ≤ 4 * N := hsize
      _ ≤ 4 * (N * z) := Nat.mul_le_mul_left 4 hle1
      _ < 4 * (2 * 2 ^ (m * (T + S))) := by omega
      _ = 2 ^ (m * (T + S) + 3) := by ring
  have h8' : 8 * n < m * (T + S) + 3 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h8
  have e1 : m * (T + S) = m * T + m * S := mul_add m T S
  have e2 : m * (3 * S + 8) = 3 * (m * S) + 8 * m := by ring
  have e3 : m * (5 * T) = 5 * (m * T) := by ring
  have h9 := Nat.mul_le_mul_left m hTS
  omega

theorem l3u3_suN_three_dvd_two_pow_add_one {m : ℕ} (hm : m % 2 = 1) : 3 ∣ 2 ^ m + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  rw [hk, pow_succ, pow_mul]
  have : ((2 ^ 2) ^ k * 2 + 1) % 3 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

theorem l3u3_suN_three_arith {N z m : ℕ} (hN : L3U3Order N) (hm : 1 ≤ m) (hz : Odd z)
    (hcard : ((N * z : ℕ) : ℤ) = ((2 ^ m : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 3, (((2 ^ m : ℕ) : ℤ) ^ i - (-1) ^ i)) :
    m % 2 = 1 ∧ ¬ 3 ∣ m := by
  have hm0 : m ≠ 0 := by omega
  rw [l3u3_suN_prod_Icc_two_three, show 3 * (3 - 1) / 2 = 3 by norm_num] at hcard
  have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hnat : N * z = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
    zify [h1]
    push_cast at hcard
    exact hcard
  have e2 : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e3 : (2 ^ m) ^ 3 = 8 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e2, e3] at hnat
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn2, hn3, hv2, -⟩ := l3u3_suN_param hN
  have hne4 : 4 ^ m - 1 ≠ 0 := (odd_four_pow_sub_one hm0).pos.ne'
  have hne8 : 8 ^ m + 1 ≠ 0 := by positivity
  have hz0 : z ≠ 0 := hz.pos.ne'
  have hN0 : N ≠ 0 := hN.ne_zero
  have hv : padicValNat 2 (N * z) = 3 * m := by
    have hv8 : padicValNat 2 (8 ^ m) = 3 * m := by
      rw [← two_pow_three_mul, padicValNat.prime_pow]
    rw [hnat, padicValNat.mul (by positivity) (mul_ne_zero hne4 hne8),
      padicValNat.mul hne4 hne8, hv8,
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1
        (odd_four_pow_sub_one hm0))),
      padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1
        (odd_eight_pow_add_one hm0)))]
    rfl
  rw [padicValNat.mul hN0 hz0, hv2, padicValNat.eq_zero_of_not_dvd
    (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hz)), add_zero] at hv
  have hnm : n = m := by omega
  subst hnm
  refine ⟨?_, hn3⟩
  have h9 : 9 ∣ (4 ^ n - 1) * (8 ^ n + 1) := by
    have h9' : 9 ∣ 8 ^ n * ((4 ^ n - 1) * (8 ^ n + 1)) := by
      rw [← hnat]
      exact Dvd.dvd.mul_right hN.nine_dvd z
    exact (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 9 8)).dvd_of_dvd_mul_left h9'
  have hv3 := (padicValNat_dvd_iff_le (p := 3) (n := 2) (mul_ne_zero hne4 hne8)).1
    (by simpa using h9)
  rw [padicValNat.mul hne4 hne8, padicValNat_three_four_pow_sub_one hm0 hn3] at hv3
  have h3dvd : 3 ∣ 8 ^ n + 1 := dvd_of_one_le_padicValNat (by omega)
  by_contra hcon
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have : (8 ^ n + 1) % 3 = 2 := by
    rw [hk, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  omega

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
