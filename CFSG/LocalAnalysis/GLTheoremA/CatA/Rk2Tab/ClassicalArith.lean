module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15

theorem eP_two_pow (r n : ℕ) : eP (2 ^ n) r = rk2Ord r n := by
  simp [eP, rk2Ord]

private lemma rk2Ord_pos_of_prime {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    0 < rk2Ord r n := by
  haveI : Fact r.Prime := ⟨hr⟩
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h')
  unfold rk2Ord
  refine orderOf_pos_iff.2 ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨r - 1, by have := hr.two_le; omega,
    ZMod.pow_card_sub_one_eq_one (pow_ne_zero n h2)⟩

private lemma div_half_eq (a m : ℕ) (hm : 2 ∣ m) : a / (m / 2) = 2 * a / m := by
  obtain ⟨k, rfl⟩ := hm
  rw [show 2 * k / 2 = k by omega]
  exact (Nat.mul_div_mul_left a k (by norm_num)).symm

theorem eM_two_pow_eq_orderOf (r n : ℕ) :
    eM (2 ^ n) r = orderOf (-((2 : ZMod r) ^ n)) := by
  simp only [eM]
  rw [Nat.cast_pow]
  norm_num

private lemma eS_two_pow_eq (r n : ℕ) :
    eS (2 ^ n) r = orderOf (((2 : ZMod r) ^ n) ^ 2) := by
  simp only [eS]
  rw [Nat.cast_pow]
  norm_num

private lemma eM_two_pow_of_odd {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hm : Odd (rk2Ord r n)) : eM (2 ^ n) r = 2 * rk2Ord r n := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [eM_two_pow_eq_orderOf]
  exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_odd
    (CFSG.LieType.SeitzGeneration.neg_one_ne_one_zmod hr hr2) rfl hm
    (rk2Ord_pos_of_prime hr hr2).ne'

private lemma eM_two_pow_of_four_dvd {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hm : 4 ∣ rk2Ord r n) : eM (2 ^ n) r = rk2Ord r n := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [eM_two_pow_eq_orderOf]
  exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_four_dvd rfl hm
    (rk2Ord_pos_of_prime hr hr2).ne'

private lemma eM_two_pow_of_two_mod_four {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hm : rk2Ord r n % 4 = 2) : eM (2 ^ n) r = rk2Ord r n / 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [eM_two_pow_eq_orderOf]
  exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_two_mod_four rfl hm

private lemma eS_two_pow_of_odd {r n : ℕ} (hm : Odd (rk2Ord r n)) :
    eS (2 ^ n) r = rk2Ord r n := by
  rw [eS_two_pow_eq, Nat.Coprime.orderOf_pow (y := (2 : ZMod r) ^ n) (m := 2)
    (Nat.coprime_two_right.mpr hm)]
  rfl

private lemma eS_two_pow_of_even {r n : ℕ} (hm : 2 ∣ rk2Ord r n) :
    eS (2 ^ n) r = rk2Ord r n / 2 := by
  rw [eS_two_pow_eq, orderOf_pow_of_dvd (x := (2 : ZMod r) ^ n) (by norm_num) hm]
  rfl

private lemma rkLin_true_eq (m Q r z : ℕ) :
    rkLin m true Q r z = (if eP Q r = 1 then
      m - 1 - (if ¬ r ∣ z ∧ r ∣ m ∧ 4 ≤ m ∧
        padicValNat r (Q - 1) ≤ padicValNat r m then 1 else 0)
      else m / eP Q r) := by
  simp [rkLin]

private lemma rkLin_false_eq (m Q r z : ℕ) :
    rkLin m false Q r z = (if eM Q r = 1 then
      m - 1 - (if ¬ r ∣ z ∧ r ∣ m ∧ 4 ≤ m ∧
        padicValNat r (Q + 1) ≤ padicValNat r m then 1 else 0)
      else m / eM Q r) := by
  simp [rkLin]

theorem rkLin_true_le_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .A) (z : ℕ) :
    rkLin (lab.rank + 1) true (2 ^ lab.n) r z ≤ rk2Mult lab (rk2Ord r lab.n) := by
  rw [rkLin_true_eq, eP_two_pow]
  simp only [rk2Mult, h]
  by_cases hm1 : rk2Ord r lab.n = 1
  · rw [if_pos hm1, if_pos hm1]
    split_ifs <;> omega
  · rw [if_neg hm1, if_neg hm1]

theorem rkLin_false_le_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .twA) (z : ℕ) :
    rkLin (lab.rank + 1) false (2 ^ lab.n) r z ≤ rk2Mult lab (rk2Ord r lab.n) := by
  rw [rkLin_false_eq]
  simp only [rk2Mult, h]
  by_cases hm2 : rk2Ord r lab.n = 2
  · have hm4 : rk2Ord r lab.n % 4 = 2 := by rw [hm2]
    have heM : eM (2 ^ lab.n) r = 1 := by
      rw [eM_two_pow_of_two_mod_four hr hr2 hm4, hm2]
    rw [heM, if_pos rfl, if_pos hm2]
    split_ifs <;> omega
  · by_cases hodd : rk2Ord r lab.n % 2 = 1
    · have hodd' : Odd (rk2Ord r lab.n) := Nat.odd_iff.mpr hodd
      have heM : eM (2 ^ lab.n) r = 2 * rk2Ord r lab.n := eM_two_pow_of_odd hr hr2 hodd'
      have hne : 2 * rk2Ord r lab.n ≠ 1 := by omega
      rw [heM, if_neg hne, if_neg hm2, if_neg (by omega : ¬ rk2Ord r lab.n % 4 = 2),
        if_pos hodd]
    · by_cases h4mod : rk2Ord r lab.n % 4 = 2
      · have h2dvd : 2 ∣ rk2Ord r lab.n := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have heM : eM (2 ^ lab.n) r = rk2Ord r lab.n / 2 :=
          eM_two_pow_of_two_mod_four hr hr2 h4mod
        have hne : rk2Ord r lab.n / 2 ≠ 1 := by omega
        rw [heM, if_neg hne, if_neg hm2, if_pos h4mod,
          div_half_eq (lab.rank + 1) (rk2Ord r lab.n) h2dvd]
      · have h4dvd : 4 ∣ rk2Ord r lab.n := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have heM : eM (2 ^ lab.n) r = rk2Ord r lab.n :=
          eM_two_pow_of_four_dvd hr hr2 h4dvd
        have hne : rk2Ord r lab.n ≠ 1 := by omega
        rw [heM, if_neg hne, if_neg hm2, if_neg h4mod,
          if_neg (by omega : ¬ rk2Ord r lab.n % 2 = 1)]

private lemma rk2Mult_BC {lab : GLALabel} (h : lab.tag = .B ∨ lab.tag = .C) (m : ℕ) :
    rk2Mult lab m = if m % 2 = 0 then 2 * lab.rank / m else lab.rank / m := by
  rcases h with h | h <;> simp only [rk2Mult, h]

theorem rkSp_eq_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .B ∨ lab.tag = .C) :
    rkSp lab.rank (2 ^ lab.n) r = rk2Mult lab (rk2Ord r lab.n) := by
  rw [rk2Mult_BC h]
  simp only [rkSp]
  by_cases hodd : rk2Ord r lab.n % 2 = 1
  · have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n :=
      eS_two_pow_of_odd (Nat.odd_iff.mpr hodd)
    rw [heS, if_neg (by omega : ¬ rk2Ord r lab.n % 2 = 0)]
  · have h2dvd : 2 ∣ rk2Ord r lab.n := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n / 2 := eS_two_pow_of_even h2dvd
    rw [heS, if_pos (by omega : rk2Ord r lab.n % 2 = 0),
      div_half_eq lab.rank (rk2Ord r lab.n) h2dvd]

theorem rkOmPlus_eq_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .D) :
    rkOmPlus lab.rank (2 ^ lab.n) r = rk2Mult lab (rk2Ord r lab.n) := by
  simp only [rkOmPlus, rk2Mult, h, eP_two_pow]
  by_cases hodd : rk2Ord r lab.n % 2 = 1
  · have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n :=
      eS_two_pow_of_odd (Nat.odd_iff.mpr hodd)
    have hco : Nat.Coprime (rk2Ord r lab.n) 2 :=
      Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd)
    have hfalse : ¬ (rk2Ord r lab.n ∣ 2 * lab.rank ∧ ¬ rk2Ord r lab.n ∣ lab.rank) := by
      rintro ⟨h1, h2⟩
      exact h2 (hco.dvd_of_dvd_mul_left h1)
    rw [heS, if_neg hfalse, if_neg (by omega : ¬ rk2Ord r lab.n % 2 = 0)]
  · have h2dvd : 2 ∣ rk2Ord r lab.n := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n / 2 := eS_two_pow_of_even h2dvd
    by_cases hc : rk2Ord r lab.n ∣ 2 * lab.rank ∧ ¬ rk2Ord r lab.n ∣ lab.rank
    · rw [heS, if_pos hc, if_pos (by omega : rk2Ord r lab.n % 2 = 0)]
      rw [if_pos hc]
    · rw [heS, if_neg hc, if_pos (by omega : rk2Ord r lab.n % 2 = 0)]
      rw [if_neg hc, div_half_eq lab.rank (rk2Ord r lab.n) h2dvd]

theorem rkOmMinus_eq_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .twD) :
    rkOmMinus lab.rank (2 ^ lab.n) r = rk2Mult lab (rk2Ord r lab.n) := by
  simp only [rkOmMinus, rk2Mult, h, eP_two_pow]
  by_cases hodd : rk2Ord r lab.n % 2 = 1
  · have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n :=
      eS_two_pow_of_odd (Nat.odd_iff.mpr hodd)
    rw [heS, if_neg (by omega : ¬ rk2Ord r lab.n % 2 = 0)]
  · have h2dvd : 2 ∣ rk2Ord r lab.n := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n / 2 := eS_two_pow_of_even h2dvd
    rw [heS, if_pos (by omega : rk2Ord r lab.n % 2 = 0),
      div_half_eq lab.rank (rk2Ord r lab.n) h2dvd]

private lemma rk2Cnt_G2 (m : ℕ) :
    rk2Cnt [(2, true), (6, true)] m =
      (if m ∣ 2 then 1 else 0) + (if m ∣ 6 then 1 else 0) := by
  simp [rk2Cnt, List.countP_cons]
  exact Nat.add_comm _ _

private lemma rk2Mult_G2 {lab : GLALabel} (h : lab.tag = .G2 ∨ lab.tag = .G2der) (m : ℕ) :
    rk2Mult lab m = (if m ∣ 2 then 1 else 0) + (if m ∣ 6 then 1 else 0) := by
  rcases h with h | h <;> simp only [rk2Mult, h, rk2Cnt_G2]

private lemma eq_three_or_six_of_dvd_six {m : ℕ} (h6 : m ∣ 6) (h2 : ¬ m ∣ 2) :
    m = 3 ∨ m = 6 := by
  have hle : m ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hpos : 0 < m := Nat.pos_of_dvd_of_pos h6 (by norm_num)
  interval_cases m <;> simp_all

theorem rkG2_eq_rk2Mult {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (lab : GLALabel)
    (h : lab.tag = .G2 ∨ lab.tag = .G2der) :
    rkG2 (2 ^ lab.n) r = rk2Mult lab (rk2Ord r lab.n) := by
  rw [rk2Mult_G2 h]
  have heS : eS (2 ^ lab.n) r = rk2Ord r lab.n / Nat.gcd (rk2Ord r lab.n) 2 := by
    rw [eS_two_pow_eq, orderOf_pow' ((2 : ZMod r) ^ lab.n) (by norm_num)]
    rfl
  simp only [rkG2]
  by_cases h2 : rk2Ord r lab.n ∣ 2
  · have hs : eS (2 ^ lab.n) r = 1 := by
      rw [heS, Nat.gcd_eq_left h2]
      exact Nat.div_self (Nat.pos_of_dvd_of_pos h2 (by norm_num))
    rw [hs, if_pos rfl, if_pos h2, if_pos (dvd_trans h2 (by norm_num : 2 ∣ 6))]
  · by_cases h6 : rk2Ord r lab.n ∣ 6
    · rcases eq_three_or_six_of_dvd_six h6 h2 with hm | hm
      · have hs : eS (2 ^ lab.n) r = 3 := by
          rw [heS, hm]
          norm_num
        rw [hs, if_neg (by norm_num : ¬ (3 : ℕ) = 1), if_pos rfl, if_neg h2, if_pos h6]
      · have hs : eS (2 ^ lab.n) r = 3 := by
          rw [heS, hm]
          norm_num
        rw [hs, if_neg (by norm_num : ¬ (3 : ℕ) = 1), if_pos rfl, if_neg h2, if_pos h6]
    · have hs1 : eS (2 ^ lab.n) r ≠ 1 := by
        rw [heS]
        intro h
        apply h6
        have hg : Nat.gcd (rk2Ord r lab.n) 2 ∣ rk2Ord r lab.n := Nat.gcd_dvd_left _ _
        have hmul := Nat.div_mul_cancel hg
        rw [h, one_mul] at hmul
        rw [← hmul]
        exact dvd_trans (Nat.gcd_dvd_right _ _) (by norm_num : 2 ∣ 6)
      have hs3 : eS (2 ^ lab.n) r ≠ 3 := by
        rw [heS]
        intro h
        apply h6
        have hg : Nat.gcd (rk2Ord r lab.n) 2 ∣ rk2Ord r lab.n := Nat.gcd_dvd_left _ _
        have hmul := Nat.div_mul_cancel hg
        rw [h] at hmul
        rw [← hmul]
        simpa using mul_dvd_mul_left 3 (Nat.gcd_dvd_right (rk2Ord r lab.n) 2)
      rw [if_neg hs1, if_neg hs3, if_neg (fun h => h6 (dvd_trans h (by norm_num : 2 ∣ 6))),
        if_neg h6]

end CFSG.LocalAnalysis.GLTheoremA
