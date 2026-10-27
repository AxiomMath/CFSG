module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Open

theorem eq_of_two_pow_mul_odd' {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b := by
  have h2 := congrArg (padicValNat 2) h
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  have hs2 : ¬ 2 ∣ s := by have := Nat.odd_iff.mp hs; omega
  rwa [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
    padicValNat.eq_zero_of_not_dvd hs2, add_zero, add_zero] at h2

theorem not_smallType_of_two_adic {X : Type} [Group X] (hZ : center X = ⊥) {N m : ℕ}
    (hm : Odd m) (hX : Nat.card X = 2 ^ N * m) (hN : 2 ≤ N) (hN3 : N ≠ 3) (hN6 : N ≠ 6)
    (hlt : Nat.card X < 2 ^ (3 * N - 3)) : ¬ SmallType X := by
  refine not_smallType_of_card hZ (fun r hr => ?_) ?_ ?_
  · exact two_mul_ne_of_two_adic (by omega) hm hX (hlt.trans_le (pow_le_two_adic_bound hN)) hr
  · intro h
    rw [h, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at hX
    exact hN3 (eq_of_two_pow_mul_odd' hm (by decide) hX.symm)
  · intro h
    rw [h, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at hX
    exact hN6 (eq_of_two_pow_mul_odd' hm (by decide) hX.symm)

section Factors

variable {e : ℕ}

theorem two_le_two_pow (he : 1 ≤ e) : 2 ≤ 2 ^ e :=
  (pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by norm_num) he)

theorem odd_two_pow_pow_sub_one (he : 1 ≤ e) {k : ℕ} (hk : 1 ≤ k) : Odd ((2 ^ e) ^ k - 1) := by
  rw [← pow_mul]
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by positivity⟩) odd_one

theorem odd_two_pow_pow_add_one (he : 1 ≤ e) {k : ℕ} (hk : 1 ≤ k) : Odd ((2 ^ e) ^ k + 1) := by
  rw [← pow_mul]
  exact (Nat.even_pow.2 ⟨even_two, by positivity⟩).add_one

theorem pow_sub_one_le (q k : ℕ) : q ^ k - 1 ≤ q ^ k := Nat.sub_le _ _

theorem pow_add_one_le {q : ℕ} (hq : 2 ≤ q) (k : ℕ) : q ^ k + 1 ≤ q ^ (k + 1) := by
  have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  calc q ^ k + 1 ≤ q ^ k + q ^ k := by omega
    _ = 2 * q ^ k := by ring
    _ ≤ q * q ^ k := Nat.mul_le_mul_right _ hq
    _ = q ^ (k + 1) := by ring

theorem two_pow_pow (e a : ℕ) : (2 ^ e) ^ a = 2 ^ (a * e) := by
  rw [← pow_mul, mul_comm]

end Factors


theorem not_smallType_of_pow_mul {X : Type} [Group X] (hZ : center X = ⊥) {e a b P : ℕ}
    (hP : Odd P) (hPle : P ≤ (2 ^ e) ^ b) (hX : Nat.card X = (2 ^ e) ^ a * P)
    (hab : (a + b) * e < 3 * (a * e) - 3) (ha : 2 ≤ a * e) (h3 : a * e ≠ 3) (h6 : a * e ≠ 6) :
    ¬ SmallType X := by
  refine not_smallType_of_two_adic hZ hP (N := a * e) ?_ ha h3 h6 ?_
  · rw [hX, two_pow_pow]
  · rw [hX]
    calc (2 ^ e) ^ a * P ≤ (2 ^ e) ^ a * (2 ^ e) ^ b := Nat.mul_le_mul_left _ hPle
      _ = 2 ^ ((a + b) * e) := by rw [← pow_add, two_pow_pow]
      _ < 2 ^ (3 * (a * e) - 3) := Nat.pow_lt_pow_right (by norm_num) hab

section Families

variable {X : Type} [Group X] (hZ : center X = ⊥) {e : ℕ} (he : 1 ≤ e)
include hZ he

theorem not_smallType_of_card_ordG2 (he2 : 2 ≤ e) (hX : Nat.card X = ordG2 (2 ^ e)) :
    ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have hm : Odd ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
    (odd_two_pow_pow_sub_one he (by norm_num)).mul (odd_two_pow_pow_sub_one he (by norm_num))
  refine not_smallType_of_two_adic hZ hm (N := 6 * e) ?_ (by omega) (by omega) (by omega) ?_
  · rw [hX, ordG2, ← two_pow_pow, ← hq, mul_assoc]
  · have h1 : (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 :=
      Nat.mul_le_mul (pow_sub_one_le q 6) (pow_sub_one_le q 2)
    have h2 : (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 8 := by
      have : (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 6 * q ^ 2 :=
        Nat.mul_lt_mul_of_le_of_lt (pow_sub_one_le q 6)
          (Nat.sub_lt (pow_pos (by omega) 2) one_pos) (by positivity)
      calc _ < q ^ 6 * q ^ 2 := this
        _ = q ^ 8 := by ring
    rw [hX, ordG2, mul_assoc]
    calc q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) < q ^ 6 * q ^ 8 :=
          Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 2 ^ (14 * e) := by rw [← pow_add, hq, two_pow_pow]
      _ ≤ 2 ^ (3 * (6 * e) - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem not_smallType_of_card_ordF4 (hX : Nat.card X = ordF4 (2 ^ e)) : ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  refine not_smallType_of_pow_mul hZ (e := e) (a := 24) (b := 28)
    (((o 12 (by norm_num)).mul (o 8 (by norm_num))).mul ((o 6 (by norm_num)).mul
      (o 2 (by norm_num)))) ?_ ?_ (by omega) (by omega) (by omega) (by omega)
  · calc (q ^ 12 - 1) * (q ^ 8 - 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) ≤
          q ^ 12 * q ^ 8 * (q ^ 6 * q ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (pow_sub_one_le q 12) (pow_sub_one_le q 8))
          (Nat.mul_le_mul (pow_sub_one_le q 6) (pow_sub_one_le q 2))
      _ = q ^ 28 := by ring
  · rw [hX, ordF4]
    ring

theorem not_smallType_of_card_ordE6 (hX : Nat.card X = ordE6 (2 ^ e)) : ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  set A := (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
    with hA
  set d := Nat.gcd 3 (q - 1) with hd
  have hAodd : Odd A := by
    simp only [hA]
    exact (((((o 12 (by norm_num)).mul (o 9 (by norm_num))).mul (o 8 (by norm_num))).mul
      (o 6 (by norm_num))).mul (o 5 (by norm_num))).mul (o 2 (by norm_num))
  have hdA : d ∣ A := by
    have h1 : d ∣ q ^ 2 - 1 := (Nat.gcd_dvd_right 3 (q - 1)).trans (by
      simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2)
    exact h1.trans (dvd_mul_left _ _)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
  refine not_smallType_of_pow_mul hZ (e := e) (a := 36) (b := 42) (P := A / d)
    (Nat.odd_mul.mp (show Odd (d * (A / d)) by rw [Nat.mul_div_cancel' hdA]; exact hAodd)).2
    ?_ ?_
    (by omega) (by omega) (by omega) (by omega)
  · calc A / d ≤ A := Nat.div_le_self _ _
      _ ≤ q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (pow_sub_one_le q 12) (pow_sub_one_le q 9)) (pow_sub_one_le q 8))
          (pow_sub_one_le q 6)) (pow_sub_one_le q 5)) (pow_sub_one_le q 2)
      _ = q ^ 42 := by ring
  · rw [hX, ordE6, ← hd, show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) = q ^ 36 * A by rw [hA]; ring, Nat.mul_div_assoc _ hdA]

theorem not_smallType_of_card_ordTwistedE6 (hX : Nat.card X = ordTwistedE6 (2 ^ e)) :
    ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  have o' : ∀ k, 1 ≤ k → Odd (q ^ k + 1) := fun k hk => odd_two_pow_pow_add_one he hk
  set A := (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
    with hA
  set d := Nat.gcd 3 (q + 1) with hd
  have hAodd : Odd A := by
    simp only [hA]
    exact (((((o 12 (by norm_num)).mul (o' 9 (by norm_num))).mul (o 8 (by norm_num))).mul
      (o 6 (by norm_num))).mul (o' 5 (by norm_num))).mul (o 2 (by norm_num))
  have hdA : d ∣ A := by
    have h1 : d ∣ q ^ 2 - 1 := (Nat.gcd_dvd_right 3 (q + 1)).trans ⟨q - 1, by
      rw [show q ^ 2 = q * q by ring]
      have : 1 ≤ q := by omega
      zify [this, Nat.one_le_iff_ne_zero.2 (show q * q ≠ 0 by positivity)]
      ring⟩
    exact h1.trans (dvd_mul_left _ _)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
  refine not_smallType_of_pow_mul hZ (e := e) (a := 36) (b := 44) (P := A / d)
    (Nat.odd_mul.mp (show Odd (d * (A / d)) by rw [Nat.mul_div_cancel' hdA]; exact hAodd)).2
    ?_ ?_
    (by omega) (by omega) (by omega) (by omega)
  · calc A / d ≤ A := Nat.div_le_self _ _
      _ ≤ q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (pow_sub_one_le q 12) (pow_add_one_le hq2 9)) (pow_sub_one_le q 8))
          (pow_sub_one_le q 6)) (pow_add_one_le hq2 5)) (pow_sub_one_le q 2)
      _ = q ^ 44 := by ring
  · rw [hX, ordTwistedE6, ← hd, show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) = q ^ 36 * A by rw [hA]; ring,
      Nat.mul_div_assoc _ hdA]

theorem not_smallType_of_card_ordE7 (hX : Nat.card X = ordE7 (2 ^ e)) : ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  have hg : Nat.gcd 2 (q - 1) = 1 := by
    have := o 1 le_rfl
    rw [pow_one] at this
    exact Nat.coprime_two_left.mpr this
  refine not_smallType_of_pow_mul hZ (e := e) (a := 63) (b := 70)
    ((((((o 18 (by norm_num)).mul (o 14 (by norm_num))).mul (o 12 (by norm_num))).mul
      (o 10 (by norm_num))).mul (o 8 (by norm_num))).mul ((o 6 (by norm_num)).mul
      (o 2 (by norm_num)))) ?_ ?_ (by omega) (by omega) (by omega) (by omega)
  · calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
          ((q ^ 6 - 1) * (q ^ 2 - 1)) ≤
          q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * (q ^ 6 * q ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (pow_sub_one_le q 18) (pow_sub_one_le q 14)) (pow_sub_one_le q 12))
          (pow_sub_one_le q 10)) (pow_sub_one_le q 8))
          (Nat.mul_le_mul (pow_sub_one_le q 6) (pow_sub_one_le q 2))
      _ = q ^ 70 := by ring
  · rw [hX, ordE7, hg, Nat.div_one]
    ring

theorem not_smallType_of_card_ordE8 (hX : Nat.card X = ordE8 (2 ^ e)) : ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  refine not_smallType_of_pow_mul hZ (e := e) (a := 120) (b := 128)
    (((((((o 30 (by norm_num)).mul (o 24 (by norm_num))).mul (o 20 (by norm_num))).mul
      (o 18 (by norm_num))).mul (o 14 (by norm_num))).mul (o 12 (by norm_num))).mul
      ((o 8 (by norm_num)).mul (o 2 (by norm_num)))) ?_ ?_
    (by omega) (by omega) (by omega) (by omega)
  · calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
          (q ^ 12 - 1) * ((q ^ 8 - 1) * (q ^ 2 - 1)) ≤
          q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * (q ^ 8 * q ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul (pow_sub_one_le q 30) (pow_sub_one_le q 24)) (pow_sub_one_le q 20))
          (pow_sub_one_le q 18)) (pow_sub_one_le q 14)) (pow_sub_one_le q 12))
          (Nat.mul_le_mul (pow_sub_one_le q 8) (pow_sub_one_le q 2))
      _ = q ^ 128 := by ring
  · rw [hX, ordE8]
    ring

theorem not_smallType_of_card_ordTrialityD4 (hX : Nat.card X = ordTrialityD4 (2 ^ e)) :
    ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  have hev : Even q := by rw [hq]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hodd8 : Odd (q ^ 8 + q ^ 4 + 1) := by
    have h8 : Even (q ^ 8) := Nat.even_pow.2 ⟨hev, by norm_num⟩
    have h4 : Even (q ^ 4) := Nat.even_pow.2 ⟨hev, by norm_num⟩
    exact (h8.add h4).add_one
  have h9 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
    have h48 : q ^ 4 + 1 ≤ q ^ 8 := by
      have : q ^ 4 + 1 ≤ q ^ 5 := pow_add_one_le hq2 4
      exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    have : q ^ 8 + q ^ 8 ≤ q ^ 9 := by
      calc q ^ 8 + q ^ 8 = 2 * q ^ 8 := by ring
        _ ≤ q * q ^ 8 := Nat.mul_le_mul_right _ hq2
        _ = q ^ 9 := by ring
    omega
  refine not_smallType_of_pow_mul hZ (e := e) (a := 12) (b := 17)
    (hodd8.mul ((o 6 (by norm_num)).mul (o 2 (by norm_num)))) ?_ ?_
    (by omega) (by omega) (by omega) (by omega)
  · calc (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) ≤ q ^ 9 * (q ^ 6 * q ^ 2) :=
        Nat.mul_le_mul h9 (Nat.mul_le_mul (pow_sub_one_le q 6) (pow_sub_one_le q 2))
      _ = q ^ 17 := by ring
  · rw [hX, ordTrialityD4]
    ring

theorem not_smallType_of_card_ordTwistedF4 (he3 : 3 ≤ e)
    (hX : Nat.card X = ordTwistedF4 (2 ^ e)) : ¬ SmallType X := by
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := two_le_two_pow he
  have o : ∀ k, 1 ≤ k → Odd (q ^ k - 1) := fun k hk => odd_two_pow_pow_sub_one he hk
  have o' : ∀ k, 1 ≤ k → Odd (q ^ k + 1) := fun k hk => odd_two_pow_pow_add_one he hk
  have o1 : Odd (q - 1) := by simpa using o 1 le_rfl
  refine not_smallType_of_pow_mul hZ (e := e) (a := 12) (b := 16)
    ((((o' 6 (by norm_num)).mul (o 4 (by norm_num))).mul (o' 3 (by norm_num))).mul o1) ?_ ?_
    (by omega) (by omega) (by omega) (by omega)
  · calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 * q :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (pow_add_one_le hq2 6)
          (pow_sub_one_le q 4)) (pow_add_one_le hq2 3)) (Nat.sub_le q 1)
      _ = q ^ 16 := by ring
  · rw [hX, ordTwistedF4]
    ring

end Families

theorem not_smallType_of_card_ordTits {X : Type} [Group X] (hZ : center X = ⊥)
    (hX : Nat.card X = ordTits) : ¬ SmallType X :=
  not_smallType_of_two_adic hZ (N := 11) (m := 3 ^ 3 * 5 ^ 2 * 13) (by decide)
    (by rw [hX, ordTits]; ring) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hX, ordTits]; norm_num)

end CFSG.ComponentClassification.ExcSelector
