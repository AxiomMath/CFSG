module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2TD4B

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof (lieOrderCofactor lieOrderNumerator_eq)
open Finset

section TD4C

theorem prod_sub_one_ge {q : ℕ} (hq : 16 ≤ q) (s : Finset ℕ) (hs : ∀ i ∈ s, 1 ≤ i) :
    15 ^ s.card * q ^ (∑ i ∈ s, i) ≤ 16 ^ s.card * ∏ i ∈ s, (q ^ i - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have ha1 : 1 ≤ a := hs a (Finset.mem_insert_self a s)
    have hqa : 16 ≤ q ^ a := by
      calc 16 ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ a := Nat.pow_le_pow_right (by omega) ha1
    have h2 : 15 * q ^ a ≤ 16 * (q ^ a - 1) := by omega
    calc 15 ^ (s.card + 1) * q ^ (a + ∑ i ∈ s, i)
        = (15 ^ s.card * q ^ (∑ i ∈ s, i)) * (15 * q ^ a) := by ring
      _ ≤ (16 ^ s.card * ∏ i ∈ s, (q ^ i - 1)) * (16 * (q ^ a - 1)) := Nat.mul_le_mul h1 h2
      _ = 16 ^ (s.card + 1) * ((q ^ a - 1) * ∏ i ∈ s, (q ^ i - 1)) := by ring

theorem sum_Icc_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, i = n * (n - 1) / 2 + n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

theorem cof_ge {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {n q : ℕ} (hn : 1 ≤ n) (hq : 16 ≤ q) :
    15 ^ (n - 1) * q ^ (cofE t n) ≤ 16 ^ (n - 1) * lieOrderCofactor t n q := by
  have hcard : (Finset.Icc 2 n).card = n - 1 := by simp
  have hprod := prod_sub_one_ge hq (Finset.Icc 2 n) (fun i hi => by
    simp only [Finset.mem_Icc] at hi
    omega)
  rw [hcard, sum_Icc_two n hn] at hprod
  rcases ht with rfl | rfl
  · simpa [cofE, lieOrderCofactor] using hprod
  · have h2 : ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) ≤
        ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) :=
      Finset.prod_le_prod' (fun i _ => by split_ifs <;> omega)
    calc 15 ^ (n - 1) * q ^ (cofE .PSU n) ≤ 16 ^ (n - 1) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := by
          simpa [cofE] using hprod
      _ ≤ 16 ^ (n - 1) * lieOrderCofactor .PSU n q := Nat.mul_le_mul_left _ (by
          simpa [lieOrderCofactor] using h2)

theorem td4_lt {e M : ℕ} (he : 2 ≤ e)
    (hM : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    M < 2 * (2 ^ e) ^ 28 := by
  rw [order_TD4 hM]
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 2 ^ e = Q at h4 ⊢
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hBC : (Q ^ 6 - 1) * (Q ^ 2 - 1) < Q ^ 8 := by
    zify [h2, h6]
    have hQ : (4 : ℤ) ≤ Q := by exact_mod_cast h4
    have p2 : (0 : ℤ) < (Q : ℤ) ^ 2 := by positivity
    have p6 : (0 : ℤ) < (Q : ℤ) ^ 6 := by positivity
    nlinarith
  have hA : Q ^ 8 + Q ^ 4 + 1 ≤ 2 * Q ^ 8 := by
    have : Q ^ 4 + 1 ≤ Q ^ 8 := by
      have h44 : Q ^ 4 ≤ Q ^ 8 / 2 := by
        have : 2 * Q ^ 4 ≤ Q ^ 8 := by
          have h4' : 2 ≤ Q ^ 4 := by
            calc 2 ≤ 4 := by norm_num
              _ ≤ Q := h4
              _ = Q ^ 1 := (pow_one Q).symm
              _ ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          calc 2 * Q ^ 4 ≤ Q ^ 4 * Q ^ 4 := Nat.mul_le_mul_right _ h4'
            _ = Q ^ 8 := by ring
        omega
      have h1 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    omega
  have hQ12 : 0 < Q ^ 12 := by positivity
  calc Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)
      = Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * ((Q ^ 6 - 1) * (Q ^ 2 - 1)) := by ring
    _ < Q ^ 12 * (2 * Q ^ 8) * Q ^ 8 := by
        apply Nat.mul_lt_mul_of_le_of_lt (Nat.mul_le_mul_left _ hA) hBC (by positivity)
    _ = 2 * (Q ^ 28) := by ring

theorem td4_excl_gap {t : StatedLieTag} {n f e M g : ℕ} (he : 2 ≤ e)
    (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e))
    (ht : t = .PSL ∨ t = .PSU) (hf : 4 ≤ f)
    (hg : 28 * e + g ≤ f * (lieSylowExponent t n + cofE t n))
    (hnum : 2 * n * 16 ^ (n - 1) ≤ 15 ^ (n - 1) * 2 ^ g) : False := by
  have hn : 1 ≤ n := by
    rcases ht with rfl | rfl
    · have := hadm.2.2.1
      omega
    · have := hadm.2.2.1
      omega
  have hq16 : 16 ≤ 2 ^ f := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hMeq := hM
  rw [lieOrderNumerator_eq hadm] at hMeq
  have hDle : lieOrderDivisor t n (2 ^ f) ≤ n := by
    rcases ht with rfl | rfl <;> exact Nat.gcd_le_left _ (by omega)
  have hcof := cof_ge ht hn hq16
  have hlt := td4_lt he hM'
  have key : 15 ^ (n - 1) * (2 ^ f) ^ (lieSylowExponent t n + cofE t n) <
      2 * n * 16 ^ (n - 1) * (2 ^ e) ^ 28 := by
    calc 15 ^ (n - 1) * (2 ^ f) ^ (lieSylowExponent t n + cofE t n)
        = (2 ^ f) ^ lieSylowExponent t n * (15 ^ (n - 1) * (2 ^ f) ^ cofE t n) := by ring
      _ ≤ (2 ^ f) ^ lieSylowExponent t n * (16 ^ (n - 1) * lieOrderCofactor t n (2 ^ f)) :=
          Nat.mul_le_mul_left _ hcof
      _ = 16 ^ (n - 1) * (M * lieOrderDivisor t n (2 ^ f)) := by rw [hMeq]; ring
      _ ≤ 16 ^ (n - 1) * (M * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hDle)
      _ < 16 ^ (n - 1) * (2 * (2 ^ e) ^ 28 * n) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
          exact Nat.mul_lt_mul_of_pos_right hlt (by omega)
      _ = 2 * n * 16 ^ (n - 1) * (2 ^ e) ^ 28 := by ring
  have hpow : (2 ^ e) ^ 28 * 2 ^ g ≤ (2 ^ f) ^ (lieSylowExponent t n + cofE t n) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by linarith)
  have h1 : 15 ^ (n - 1) * ((2 ^ e) ^ 28 * 2 ^ g) ≤
      15 ^ (n - 1) * (2 ^ f) ^ (lieSylowExponent t n + cofE t n) := Nat.mul_le_mul_left _ hpow
  have h2 : 2 * n * 16 ^ (n - 1) * (2 ^ e) ^ 28 ≤ 15 ^ (n - 1) * 2 ^ g * (2 ^ e) ^ 28 :=
    Nat.mul_le_mul_right _ hnum
  have h3 : 15 ^ (n - 1) * 2 ^ g * (2 ^ e) ^ 28 = 15 ^ (n - 1) * ((2 ^ e) ^ 28 * 2 ^ g) := by ring
  omega

theorem td4_excl_L6 {f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible .PSL 6 2 f)
    (hM : M * lieOrderDivisor .PSL 6 (2 ^ f) = lieOrderNumerator .PSL 6 (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hN : lieSylowExponent .PSL 6 = 15 := by decide
  have hcE : cofE .PSL 6 = 20 := by decide
  rw [hN] at hv
  have hf4 : 4 ∣ f := by omega
  have h3 : 3 ∣ 2 ^ f - 1 := by
    obtain ⟨j, rfl⟩ := hf4
    have h16 : 2 ^ (4 * j) = 16 ^ j := by rw [pow_mul]; norm_num
    rw [h16]
    have := Nat.sub_one_dvd_pow_sub_one 16 j
    exact dvd_trans (by norm_num) this
  have hD : 3 ≤ lieOrderDivisor .PSL 6 (2 ^ f) := by
    show 3 ≤ Nat.gcd 6 (2 ^ f - 1)
    have hd : 3 ∣ Nat.gcd 6 (2 ^ f - 1) := Nat.dvd_gcd (by norm_num) h3
    have hpos : 0 < Nat.gcd 6 (2 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    exact Nat.le_of_dvd hpos hd
  have hMeq := hM
  rw [lieOrderNumerator_eq hadm, hN] at hMeq
  have hcof := cof_lt_pow hadm
  rw [hcE] at hcof
  have hlow := td4_ge he hM'
  have hq35 : (2 ^ f) ^ 35 = (2 ^ e) ^ 28 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hlt : M * lieOrderDivisor .PSL 6 (2 ^ f) < (2 ^ e) ^ 28 := by
    rw [hMeq, ← hq35]
    calc (2 ^ f) ^ 15 * lieOrderCofactor .PSL 6 (2 ^ f) < (2 ^ f) ^ 15 * (2 ^ f) ^ 20 :=
          Nat.mul_lt_mul_of_pos_left hcof (by positivity)
      _ = (2 ^ f) ^ 35 := by ring
  have h3M : M * 3 ≤ M * lieOrderDivisor .PSL 6 (2 ^ f) := Nat.mul_le_mul_left _ hD
  omega

theorem td4_excl_U6 {f e M : ℕ} (he : 2 ≤ e) (hadm : StatedLieAdmissible .PSU 6 2 f)
    (hM : M * lieOrderDivisor .PSU 6 (2 ^ f) = lieOrderNumerator .PSU 6 (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e)) :
    False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hN : lieSylowExponent .PSU 6 = 15 := by decide
  rw [hN] at hv
  obtain ⟨j, rfl, rfl⟩ : ∃ j, f = 4 * j ∧ e = 5 * j := ⟨e / 5, by omega, by omega⟩
  have hj : 1 ≤ j := by omega
  have hx : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hev : Even (2 ^ j) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hD : lieOrderDivisor .PSU 6 (2 ^ (4 * j)) = 1 := by
    show Nat.gcd 6 (2 ^ (4 * j) + 1) = 1
    have h16 : 2 ^ (4 * j) = 16 ^ j := by rw [pow_mul]; norm_num
    have hodd : Odd (2 ^ (4 * j) + 1) := by
      have : Even (2 ^ (4 * j)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact this.add_one
    have h3 : ¬ 3 ∣ 2 ^ (4 * j) + 1 := by
      rw [h16]
      have : 16 ^ j % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      omega
    have c2 : Nat.Coprime 2 (2 ^ (4 * j) + 1) := Nat.coprime_two_left.mpr hodd
    have c3 : Nat.Coprime 3 (2 ^ (4 * j) + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have c6 : Nat.Coprime 6 (2 ^ (4 * j) + 1) := by
      have := Nat.Coprime.mul_left c2 c3
      simpa using this
    exact c6
  rw [hD, mul_one] at hM
  have hM2 := order_TD4 hM'
  rw [pow_mul'] at hM hM2
  generalize 2 ^ j = x at hx hM hM2
  have e1 : M = x ^ 60 * ((x ^ 8 - 1) * (x ^ 12 + 1) * (x ^ 16 - 1) * (x ^ 20 + 1) * (x ^ 24 - 1)) := by
    rw [hM]
    have hp : lieOrderNumerator .PSU 6 (x ^ 4) = (x ^ 4) ^ 15 *
        (((x ^ 4) ^ 2 - 1) * ((x ^ 4) ^ 3 + 1) * ((x ^ 4) ^ 4 - 1) * ((x ^ 4) ^ 5 + 1) *
          ((x ^ 4) ^ 6 - 1)) := by
      simp [lieOrderNumerator, Finset.prod_Icc_succ_top, Nat.even_iff]
    rw [hp]
    have a1 : (x ^ 4) ^ 2 = x ^ 8 := by ring
    have a2 : (x ^ 4) ^ 3 = x ^ 12 := by ring
    have a3 : (x ^ 4) ^ 4 = x ^ 16 := by ring
    have a4 : (x ^ 4) ^ 5 = x ^ 20 := by ring
    have a5 : (x ^ 4) ^ 6 = x ^ 24 := by ring
    have a6 : (x ^ 4) ^ 15 = x ^ 60 := by ring
    rw [a1, a2, a3, a4, a5, a6]
  have e2 : M = x ^ 60 * ((x ^ 40 + x ^ 20 + 1) * (x ^ 30 - 1) * (x ^ 10 - 1)) := by
    rw [hM2]
    have b1 : (x ^ 5) ^ 12 = x ^ 60 := by ring
    have b2 : (x ^ 5) ^ 8 = x ^ 40 := by ring
    have b3 : (x ^ 5) ^ 4 = x ^ 20 := by ring
    have b4 : (x ^ 5) ^ 6 = x ^ 30 := by ring
    have b5 : (x ^ 5) ^ 2 = x ^ 10 := by ring
    rw [b1, b2, b3, b4, b5]
    ring
  have hx60 : 0 < x ^ 60 := by positivity
  have key := Nat.eq_of_mul_eq_mul_left hx60 (e1.symm.trans e2)
  have h8 : 1 ≤ x ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h10 : 1 ≤ x ^ 10 := Nat.one_le_pow _ _ (by omega)
  have h16 : 1 ≤ x ^ 16 := Nat.one_le_pow _ _ (by omega)
  have h24 : 1 ≤ x ^ 24 := Nat.one_le_pow _ _ (by omega)
  have h30 : 1 ≤ x ^ 30 := Nat.one_le_pow _ _ (by omega)
  zify [h8, h10, h16, h24, h30] at key
  have hxz : (2 : ℤ) ≤ x := by exact_mod_cast hx
  generalize (x : ℤ) = X at key hxz
  have m1 : X ^ 8 - 1 ≡ -1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
  have m2 : X ^ 12 + 1 ≡ 1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 4, by ring⟩
  have m3 : X ^ 16 - 1 ≡ -1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 8, by ring⟩
  have m4 : X ^ 20 + 1 ≡ 1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 12, by ring⟩
  have m5 : X ^ 24 - 1 ≡ -1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 16, by ring⟩
  have n1 : X ^ 40 + X ^ 20 + 1 ≡ 1 [ZMOD X ^ 8] :=
    Int.modEq_iff_dvd.2 ⟨-X ^ 32 - X ^ 12, by ring⟩
  have n2 : X ^ 30 - 1 ≡ -1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 22, by ring⟩
  have n3 : X ^ 10 - 1 ≡ -1 [ZMOD X ^ 8] := Int.modEq_iff_dvd.2 ⟨-X ^ 2, by ring⟩
  have hU := (((m1.mul m2).mul m3).mul m4).mul m5
  have hT := (n1.mul n2).mul n3
  rw [key] at hU
  have h := hU.symm.trans hT
  have h' : (-1 : ℤ) ≡ 1 [ZMOD X ^ 8] := by simpa using h
  have hd : X ^ 8 ∣ 1 - (-1) := Int.modEq_iff_dvd.1 h'
  have hle : X ^ 8 ≤ 2 := Int.le_of_dvd (by norm_num) (by simpa using hd)
  have h2 : (2 : ℤ) ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ (by norm_num) hxz 8
  norm_num at h2
  omega

theorem td4_excl_lu {t : StatedLieTag} {n f e M : ℕ} (he : 2 ≤ e)
    (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor .trialityD4 0 (2 ^ e) = lieOrderNumerator .trialityD4 0 (2 ^ e))
    (ht : t = .PSL ∨ t = .PSU) : False := by
  have hadm' : StatedLieAdmissible .trialityD4 0 2 e := ⟨Nat.prime_two, by omega, rfl⟩
  have hv := v2_eq_of_two hadm hM hadm' hM'
  rw [sylowExp_TD4] at hv
  have hn2 : 2 ≤ n := by
    rcases ht with rfl | rfl
    · have := hadm.2.2.1
      omega
    · have := hadm.2.2.1
      omega
  have hf1 : 1 ≤ f := hadm.2.1
  by_cases h7 : 7 ≤ n
  · refine td4_excl_crude he hadm hM hM' ?_
    have h2N : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
    have hmul : 7 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ h7
    rcases ht with rfl | rfl <;> simp only [cofE, lieSylowExponent] <;> omega
  · obtain ⟨hn, -⟩ : n ≤ 6 ∧ True := ⟨by omega, trivial⟩
    interval_cases n
    ·
      have hN : lieSylowExponent t 2 = 1 := by rcases ht with rfl | rfl <;> decide
      have hc : cofE t 2 = 2 := by rcases ht with rfl | rfl <;> decide
      rw [hN] at hv
      refine td4_excl_gap he hadm hM hM' ht (g := 8) (by omega) ?_ (by norm_num)
      rw [hN, hc]
      omega
    ·
      have hN : lieSylowExponent t 3 = 3 := by rcases ht with rfl | rfl <;> decide
      have hc : cofE t 3 = 5 := by rcases ht with rfl | rfl <;> decide
      rw [hN] at hv
      refine td4_excl_gap he hadm hM hM' ht (g := 8) (by omega) ?_ (by norm_num)
      rw [hN, hc]
      omega
    ·
      have hN : lieSylowExponent t 4 = 6 := by rcases ht with rfl | rfl <;> decide
      have hc : cofE t 4 = 9 := by rcases ht with rfl | rfl <;> decide
      rw [hN] at hv
      refine td4_excl_gap he hadm hM hM' ht (g := 4) (by omega) ?_ (by norm_num)
      rw [hN, hc]
      omega
    ·
      have hN : lieSylowExponent t 5 = 10 := by rcases ht with rfl | rfl <;> decide
      have hc : cofE t 5 = 14 := by rcases ht with rfl | rfl <;> decide
      rw [hN] at hv
      refine td4_excl_gap he hadm hM hM' ht (g := 4) (by omega) ?_ (by norm_num)
      rw [hN, hc]
      omega
    ·
      rcases ht with rfl | rfl
      · exact td4_excl_L6 he hadm hM hM'
      · exact td4_excl_U6 he hadm hM hM'

end TD4C

end CFSG.LocalAnalysis.GLTheoremA.HDesc
