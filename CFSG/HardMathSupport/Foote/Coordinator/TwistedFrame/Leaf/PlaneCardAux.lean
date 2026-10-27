module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Arith

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCard

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

section Valuations

variable {p q e : ℕ}

theorem padicValNat_pow_sub_one_eq_zero [Fact p.Prime] (hq : 1 ≤ q)
    (hord : orderOf (q : ZMod p) = e) {m : ℕ} (hm : ¬ e ∣ m) :
    padicValNat p (q ^ m - 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => hm ((dvd_pow_sub_one_iff hq hord).1 h)

theorem padicValNat_pow_eq_zero_of_orderOf [Fact p.Prime] (he : 0 < e)
    (hord : orderOf (q : ZMod p) = e) (m : ℕ) : padicValNat p (q ^ m) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h =>
    not_dvd_of_orderOf he.ne' hord ((Fact.out : p.Prime).dvd_of_dvd_pow h)

theorem padicValNat_pow_sub_one_eq [Fact p.Prime] (hodd : Odd p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = e) (he : 0 < e) {k : ℕ} (hk0 : 0 < k) (hkp : ¬ p ∣ k) :
    padicValNat p (q ^ (e * k) - 1) = padicValNat p (q ^ e - 1) := by
  have hnd : ¬ p ∣ q := not_dvd_of_orderOf he.ne' hord
  exact padicValNat_pow_mul_sub_one hodd hq he ((dvd_pow_sub_one_iff (by omega) hord).2 dvd_rfl)
    (fun h => hnd ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hk0 hkp

theorem pow_sub_one_ne_zero (hq : 2 ≤ q) {m : ℕ} (hm : 0 < m) : q ^ m - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) hm.ne')

theorem padicValNat_pow_add_one [Fact p.Prime] (hq : 2 ≤ q) {m : ℕ} (hm : 0 < m)
    (hord : orderOf (q : ZMod p) = 2 * m) :
    padicValNat p (q ^ m + 1) = padicValNat p (q ^ (2 * m) - 1) := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ (2 * m) = (q ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  have hfac : q ^ (2 * m) - 1 = (q ^ m - 1) * (q ^ m + 1) := by
    rw [h2]
    zify [h1, Nat.one_le_pow 2 (q ^ m) (by omega)]
    ring
  rw [hfac, padicValNat.mul (pow_sub_one_ne_zero hq hm) (by omega),
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := m)
      (fun h => by have := Nat.le_of_dvd hm h; omega), zero_add]

theorem padicValNat_pow_eight_add [Fact p.Prime] (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 12) :
    padicValNat p (q ^ 8 + q ^ 4 + 1) = padicValNat p (q ^ 12 - 1) := by
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hfac : q ^ 12 - 1 = (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    zify [h1, h3]
    ring
  rw [hfac, padicValNat.mul (pow_sub_one_ne_zero hq (by norm_num)) (by omega),
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 4) (by norm_num), zero_add]


theorem ten_dvd_sub_one (hp : p.Prime) (hord : orderOf (q : ZMod p) = 10) : 10 ∣ p - 1 := by
  haveI := Fact.mk hp
  have hq0 : (q : ZMod p) ≠ 0 := fun h => by
    rw [h, orderOf_zero] at hord
    omega
  have := ZMod.orderOf_dvd_card_sub_one hq0
  rwa [hord] at this

theorem pow_two_mul_sub_one (hq : 1 ≤ q) (m : ℕ) :
    q ^ (2 * m) - 1 = (q ^ m - 1) * (q ^ m + 1) := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ (2 * m) = (q ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [h2]
  zify [h1, Nat.one_le_pow 2 (q ^ m) (by omega)]
  ring

end Valuations

section Groups

variable {p q : ℕ}

theorem padicValNat_ordF4_of_orderOf_eq_six (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 6) :
    padicValNat p (CFSG.Open.ordF4 q) = 2 * padicValNat p (q ^ 6 - 1) := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hne : ∀ m, 0 < m → q ^ m - 1 ≠ 0 := fun m hm => pow_sub_one_ne_zero hq hm
  have hz : ∀ m, ¬ 6 ∣ m → padicValNat p (q ^ m - 1) = 0 := fun m hm =>
    padicValNat_pow_sub_one_eq_zero (by omega) hord hm
  have n24 : q ^ 24 ≠ 0 := pow_ne_zero _ (by omega)
  have v24 : padicValNat p (q ^ 24) = 0 :=
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord 24
  have v12 : padicValNat p (q ^ 12 - 1) = padicValNat p (q ^ 6 - 1) := by
    have h := padicValNat_pow_sub_one_eq hodd hq hord (by norm_num) (k := 2) (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    simpa using h
  have v8 := hz 8 (by norm_num)
  have v2 := hz 2 (by norm_num)
  have m1 := mul_ne_zero n24 (hne 12 (by norm_num))
  have m2 := mul_ne_zero m1 (hne 8 (by norm_num))
  have m3 := mul_ne_zero m2 (hne 6 (by norm_num))
  unfold CFSG.Open.ordF4
  rw [padicValNat.mul m3 (hne 2 (by norm_num)), padicValNat.mul m2 (hne 6 (by norm_num)),
    padicValNat.mul m1 (hne 8 (by norm_num)), padicValNat.mul n24 (hne 12 (by norm_num)),
    v24, v8, v2, v12]
  omega

theorem padicValNat_ordE6_of_orderOf_eq_six (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 6) :
    padicValNat p (CFSG.Open.ordE6 q) = 2 * padicValNat p (q ^ 6 - 1) := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hne : ∀ m, 0 < m → q ^ m - 1 ≠ 0 := fun m hm => pow_sub_one_ne_zero hq hm
  have hz : ∀ m, ¬ 6 ∣ m → padicValNat p (q ^ m - 1) = 0 := fun m hm =>
    padicValNat_pow_sub_one_eq_zero (by omega) hord hm
  have n36 : q ^ 36 ≠ 0 := pow_ne_zero _ (by omega)
  have v36 : padicValNat p (q ^ 36) = 0 :=
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord 36
  have v12 : padicValNat p (q ^ 12 - 1) = padicValNat p (q ^ 6 - 1) := by
    have h := padicValNat_pow_sub_one_eq hodd hq hord (by norm_num) (k := 2) (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    simpa using h
  have v9 := hz 9 (by norm_num)
  have v8 := hz 8 (by norm_num)
  have v5 := hz 5 (by norm_num)
  have v2 := hz 2 (by norm_num)
  have m1 := mul_ne_zero n36 (hne 12 (by norm_num))
  have m2 := mul_ne_zero m1 (hne 9 (by norm_num))
  have m3 := mul_ne_zero m2 (hne 8 (by norm_num))
  have m4 := mul_ne_zero m3 (hne 6 (by norm_num))
  have m5 := mul_ne_zero m4 (hne 5 (by norm_num))
  have hdvd : Nat.gcd 3 (q - 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) := by
    have h1 : q - 1 ∣ q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one q 2
    exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 (q - 1)).trans h1) _
  have hcop : Nat.Coprime p (Nat.gcd 3 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (q - 1))
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)))
  unfold CFSG.Open.ordE6
  rw [padicValNat.div' hcop hdvd, padicValNat.mul m5 (hne 2 (by norm_num)),
    padicValNat.mul m4 (hne 5 (by norm_num)), padicValNat.mul m3 (hne 6 (by norm_num)),
    padicValNat.mul m2 (hne 8 (by norm_num)), padicValNat.mul m1 (hne 9 (by norm_num)),
    padicValNat.mul n36 (hne 12 (by norm_num)), v36, v9, v8, v5, v2, v12]
  omega

theorem padicValNat_ordE8_of_orderOf_eq_ten (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 10) :
    padicValNat p (CFSG.Open.ordE8 q) = 2 * padicValNat p (q ^ 10 - 1) := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hne : ∀ m, 0 < m → q ^ m - 1 ≠ 0 := fun m hm => pow_sub_one_ne_zero hq hm
  have hz : ∀ m, ¬ 10 ∣ m → padicValNat p (q ^ m - 1) = 0 := fun m hm =>
    padicValNat_pow_sub_one_eq_zero (by omega) hord hm
  have n120 : q ^ 120 ≠ 0 := pow_ne_zero _ (by omega)
  have v120 : padicValNat p (q ^ 120) = 0 :=
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord 120
  have v30 : padicValNat p (q ^ 30 - 1) = padicValNat p (q ^ 10 - 1) := by
    have h := padicValNat_pow_sub_one_eq hodd hq hord (by norm_num) (k := 3) (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    simpa using h
  have v20 : padicValNat p (q ^ 20 - 1) = padicValNat p (q ^ 10 - 1) := by
    have h := padicValNat_pow_sub_one_eq hodd hq hord (by norm_num) (k := 2) (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    simpa using h
  have v24 := hz 24 (by norm_num)
  have v18 := hz 18 (by norm_num)
  have v14 := hz 14 (by norm_num)
  have v12 := hz 12 (by norm_num)
  have v8 := hz 8 (by norm_num)
  have v2 := hz 2 (by norm_num)
  have m1 := mul_ne_zero n120 (hne 30 (by norm_num))
  have m2 := mul_ne_zero m1 (hne 24 (by norm_num))
  have m3 := mul_ne_zero m2 (hne 20 (by norm_num))
  have m4 := mul_ne_zero m3 (hne 18 (by norm_num))
  have m5 := mul_ne_zero m4 (hne 14 (by norm_num))
  have m6 := mul_ne_zero m5 (hne 12 (by norm_num))
  have m7 := mul_ne_zero m6 (hne 8 (by norm_num))
  unfold CFSG.Open.ordE8
  rw [padicValNat.mul m7 (hne 2 (by norm_num)), padicValNat.mul m6 (hne 8 (by norm_num)),
    padicValNat.mul m5 (hne 12 (by norm_num)), padicValNat.mul m4 (hne 14 (by norm_num)),
    padicValNat.mul m3 (hne 18 (by norm_num)), padicValNat.mul m2 (hne 20 (by norm_num)),
    padicValNat.mul m1 (hne 24 (by norm_num)), padicValNat.mul n120 (hne 30 (by norm_num)),
    v120, v24, v18, v14, v12, v8, v2, v30, v20]
  omega

theorem padicValNat_ordE8_of_orderOf_eq_twelve (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 12) :
    padicValNat p (CFSG.Open.ordE8 q) = 2 * padicValNat p (q ^ 12 - 1) := by
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hne : ∀ m, 0 < m → q ^ m - 1 ≠ 0 := fun m hm => pow_sub_one_ne_zero hq hm
  have hz : ∀ m, ¬ 12 ∣ m → padicValNat p (q ^ m - 1) = 0 := fun m hm =>
    padicValNat_pow_sub_one_eq_zero (by omega) hord hm
  have n120 : q ^ 120 ≠ 0 := pow_ne_zero _ (by omega)
  have v120 : padicValNat p (q ^ 120) = 0 :=
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord 120
  have v24 : padicValNat p (q ^ 24 - 1) = padicValNat p (q ^ 12 - 1) := by
    have h := padicValNat_pow_sub_one_eq hodd hq hord (by norm_num) (k := 2) (by norm_num)
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
    simpa using h
  have v30 := hz 30 (by norm_num)
  have v20 := hz 20 (by norm_num)
  have v18 := hz 18 (by norm_num)
  have v14 := hz 14 (by norm_num)
  have v8 := hz 8 (by norm_num)
  have v2 := hz 2 (by norm_num)
  have m1 := mul_ne_zero n120 (hne 30 (by norm_num))
  have m2 := mul_ne_zero m1 (hne 24 (by norm_num))
  have m3 := mul_ne_zero m2 (hne 20 (by norm_num))
  have m4 := mul_ne_zero m3 (hne 18 (by norm_num))
  have m5 := mul_ne_zero m4 (hne 14 (by norm_num))
  have m6 := mul_ne_zero m5 (hne 12 (by norm_num))
  have m7 := mul_ne_zero m6 (hne 8 (by norm_num))
  unfold CFSG.Open.ordE8
  rw [padicValNat.mul m7 (hne 2 (by norm_num)), padicValNat.mul m6 (hne 8 (by norm_num)),
    padicValNat.mul m5 (hne 12 (by norm_num)), padicValNat.mul m4 (hne 14 (by norm_num)),
    padicValNat.mul m3 (hne 18 (by norm_num)), padicValNat.mul m2 (hne 20 (by norm_num)),
    padicValNat.mul m1 (hne 24 (by norm_num)), padicValNat.mul n120 (hne 30 (by norm_num)),
    v120, v30, v24, v20, v18, v14, v8, v2]
  omega

theorem padicValNat_suThree (hp : p.Prime) (hq : 2 ≤ q) (hord : orderOf (q : ZMod p) = 6) :
    padicValNat p (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) = padicValNat p (q ^ 6 - 1) := by
  haveI := Fact.mk hp
  have hne2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (mul_ne_zero hne2 (by omega)),
    padicValNat.mul hne2 (by omega), padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord,
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 2) (by norm_num),
    padicValNat_pow_add_one hq (m := 3) (by norm_num) (by simpa using hord)]
  simp

theorem padicValNat_slThreeSq (hp : p.Prime) (hq : 2 ≤ q) (hord : orderOf (q : ZMod p) = 6) :
    padicValNat p (q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1))) = padicValNat p (q ^ 6 - 1) := by
  haveI := Fact.mk hp
  have hne4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  have hne6 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (mul_ne_zero hne4 hne6),
    padicValNat.mul hne4 hne6, padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord,
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 4) (by norm_num)]
  simp

theorem padicValNat_suFive (hp : p.Prime) (hq : 2 ≤ q) (hord : orderOf (q : ZMod p) = 10) :
    padicValNat p (q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) =
      padicValNat p (q ^ 10 - 1) := by
  haveI := Fact.mk hp
  have hne2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  have hne4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  have h3 : padicValNat p (q ^ 3 + 1) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun h => ?_
    have h6 : p ∣ q ^ 6 - 1 := by
      have := pow_two_mul_sub_one (q := q) (by omega) 3
      rw [show 2 * 3 = 6 by norm_num] at this
      rw [this]
      exact Dvd.dvd.mul_left h _
    exact absurd ((dvd_pow_sub_one_iff (by omega) hord).1 h6) (by norm_num)
  rw [padicValNat.mul (pow_ne_zero _ (by omega))
      (mul_ne_zero (mul_ne_zero hne2 (by omega)) (mul_ne_zero hne4 (by omega))),
    padicValNat.mul (mul_ne_zero hne2 (by omega)) (mul_ne_zero hne4 (by omega)),
    padicValNat.mul hne2 (by omega), padicValNat.mul hne4 (by omega),
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord,
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 2) (by norm_num),
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 4) (by norm_num), h3,
    padicValNat_pow_add_one hq (m := 5) (by norm_num) (by simpa using hord)]
  simp

theorem padicValNat_trialityD4 (hp : p.Prime) (hq : 2 ≤ q) (hord : orderOf (q : ZMod p) = 12) :
    padicValNat p (CFSG.Open.ordTrialityD4 q) = padicValNat p (q ^ 12 - 1) := by
  haveI := Fact.mk hp
  have hne2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  have hne6 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero hq (by norm_num)
  have n12 : q ^ 12 ≠ 0 := pow_ne_zero _ (by omega)
  have n8 : q ^ 8 + q ^ 4 + 1 ≠ 0 := by omega
  unfold CFSG.Open.ordTrialityD4
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero n12 n8) hne6) hne2,
    padicValNat.mul (mul_ne_zero n12 n8) hne6, padicValNat.mul n12 n8,
    padicValNat_pow_eq_zero_of_orderOf (by norm_num) hord,
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 6) (by norm_num),
    padicValNat_pow_sub_one_eq_zero (by omega) hord (m := 2) (by norm_num),
    padicValNat_pow_eight_add hq hord]
  simp

end Groups


section SL

theorem card_SL_three_field {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let : Fintype F := Fintype.ofFinite F
  have h := Matrix.card_SL_mul_card_units (n := Fin 3) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Fin.prod_univ_three, ← Nat.card_eq_fintype_card] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card F - 1)
  rw [h]
  have h1 : 1 ≤ Nat.card F := by omega
  have h2' : Nat.card F ≤ Nat.card F ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : Nat.card F ^ 2 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have h4 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ h1
  have h5 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ h1
  zify [h1, h2', h3, h4, h5]
  ring

theorem card_SL_three_sq {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1)) := by
  rw [card_SL_three_field, hF]
  have e1 : (q ^ 2) ^ 3 = q ^ 6 := by ring
  have e2 : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [e1, e2]
  ring

end SL

section Commuting

variable {G : Type*} [Group G]

theorem card_mul_card_dvd_of_commute {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card A * Nat.card B ∣ Nat.card C * Nat.card ↥(A ⊓ B) := by
  let f : A × B →* G := (A.subtype).noncommCoprod (B.subtype) fun a b => hcomm a a.2 b b.2
  have h1 : Nat.card (A × B) = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card f.range ∣ Nat.card C := by
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact C.mul_mem (hA a.2) (hB b.2)
  have h3 : Nat.card f.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.1.2, ?_⟩
        invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, B.inv_mem x.2.2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have : (x.1.1 : G) * (x.1.2 : G) = 1 := hx
      have h4 : (x.1.1 : G) = (x.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left this
      rw [h4]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker]
      show (x.1 : G) * x.1⁻¹ = 1
      exact mul_inv_cancel _
    · rintro ⟨⟨a, b⟩, hab⟩
      have : (a : G) * (b : G) = 1 := hab
      have h4 : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left this
      refine Subtype.ext (Prod.ext rfl (Subtype.ext ?_))
      show ((a : G))⁻¹ = (b : G)
      rw [h4, inv_inv]
    · intro x
      rfl
  have h0 : Nat.card A * Nat.card B = Nat.card (A × B) := (Nat.card_prod A B).symm
  rw [h0, h1, h3]
  exact mul_dvd_mul_right h2 _

theorem factorization_add_le_of_commute {A B C : Subgroup G} [Finite C] (hA : A ≤ C) (hB : B ≤ C)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {p : ℕ} (hAB : ¬ p ∣ Nat.card ↥(A ⊓ B)) :
    (Nat.card A).factorization p + (Nat.card B).factorization p ≤ (Nat.card C).factorization p := by
  haveI : Finite A := Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  haveI : Finite B := Finite.of_injective (Subgroup.inclusion hB) (Subgroup.inclusion_injective hB)
  haveI : Finite ↥(A ⊓ B) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hA))
      (Subgroup.inclusion_injective _)
  have hdvd := card_mul_card_dvd_of_commute hA hB hcomm
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hI0 : Nat.card ↥(A ⊓ B) ≠ 0 := Nat.card_pos.ne'
  have h := (Nat.factorization_le_iff_dvd (mul_ne_zero hA0 hB0) (mul_ne_zero hC0 hI0)).2 hdvd p
  rw [Nat.factorization_mul hA0 hB0, Nat.factorization_mul hC0 hI0] at h
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hAB, add_zero] at h
  exact h

theorem card_inf_dvd_card_center {A B : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊓ B) ∣ Nat.card ↥(Subgroup.center ↥A) := by
  have hle : (A ⊓ B).subgroupOf A ≤ Subgroup.center ↥A := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hcomm a a.2 x hx.2)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
  exact Subgroup.card_dvd_of_le hle

end Commuting

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCard
