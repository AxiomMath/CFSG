module

public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

theorem dvd_pow_sub_one_iff {p q n d : ℕ} [Fact p.Prime] (hq : 1 ≤ q)
    (hord : orderOf (q : ZMod p) = n) : p ∣ q ^ d - 1 ↔ n ∣ d := by
  have hle : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
  rw [← ZMod.natCast_eq_zero_iff (q ^ d - 1) p, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one,
    sub_eq_zero, ← orderOf_dvd_iff_pow_eq_one, hord]

theorem not_dvd_of_orderOf {p q n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (hord : orderOf (q : ZMod p) = n) : ¬ p ∣ q := by
  intro h
  have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 h
  have h1 := pow_orderOf_eq_one (q : ZMod p)
  rw [hord, hq0, zero_pow hn] at h1
  exact zero_ne_one h1

theorem padicValNat_pow_mul_sub_one {p q m k : ℕ} [Fact p.Prime] (hodd : Odd p) (hq : 2 ≤ q)
    (hm : 0 < m) (hd : p ∣ q ^ m - 1) (hx' : ¬ p ∣ q ^ m) (hk0 : 0 < k) (hkp : ¬ p ∣ k) :
    padicValNat p (q ^ (m * k) - 1) = padicValNat p (q ^ m - 1) := by
  have hx : 1 < q ^ m := one_lt_pow₀ (by omega) hm.ne'
  have key := padicValNat.pow_sub_pow (p := p) hodd (x := q ^ m) (y := 1) hx
    (by simpa using hd) hx' hk0.ne'
  rw [one_pow, ← pow_mul] at key
  rw [key, padicValNat.eq_zero_of_not_dvd hkp, add_zero]

theorem padicValNat_ordF4_of_orderOf_eq_three {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 3) :
    padicValNat p (CFSG.Open.ordF4 q) = 2 * padicValNat p (q ^ 3 - 1) := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnd : ¬ p ∣ q := not_dvd_of_orderOf (by norm_num) hord
  have hnq : ¬ p ∣ q ^ 3 := fun h => hnd (hp.dvd_of_dvd_pow h)
  have hd : ∀ d, p ∣ q ^ d - 1 ↔ 3 ∣ d := fun d => dvd_pow_sub_one_iff (by omega) hord
  have hne : ∀ d, 0 < d → q ^ d - 1 ≠ 0 := fun d hd0 =>
    Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) hd0.ne')
  have n24 : q ^ 24 ≠ 0 := pow_ne_zero _ (by omega)
  have v24 : padicValNat p (q ^ 24) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (hp.dvd_of_dvd_pow h))
  have v8 : padicValNat p (q ^ 8 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 8).1 h; omega)
  have v2 : padicValNat p (q ^ 2 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 2).1 h; omega)
  have v12 : padicValNat p (q ^ 12 - 1) = padicValNat p (q ^ 3 - 1) := by
    have h12 : q ^ 12 = q ^ (3 * 4) := by norm_num
    rw [h12]
    exact padicValNat_pow_mul_sub_one hodd hq (by norm_num) ((hd 3).2 dvd_rfl) hnq (by norm_num)
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have v6 : padicValNat p (q ^ 6 - 1) = padicValNat p (q ^ 3 - 1) := by
    have h6 : q ^ 6 = q ^ (3 * 2) := by norm_num
    rw [h6]
    exact padicValNat_pow_mul_sub_one hodd hq (by norm_num) ((hd 3).2 dvd_rfl) hnq (by norm_num)
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have m1 := mul_ne_zero n24 (hne 12 (by norm_num))
  have m2 := mul_ne_zero m1 (hne 8 (by norm_num))
  have m3 := mul_ne_zero m2 (hne 6 (by norm_num))
  unfold CFSG.Open.ordF4
  rw [padicValNat.mul m3 (hne 2 (by norm_num)), padicValNat.mul m2 (hne 6 (by norm_num)),
    padicValNat.mul m1 (hne 8 (by norm_num)), padicValNat.mul n24 (hne 12 (by norm_num)),
    v24, v8, v2, v12, v6]
  omega

theorem padicValNat_ordE8_of_orderOf_eq_five {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hord : orderOf (q : ZMod p) = 5) :
    padicValNat p (CFSG.Open.ordE8 q) = 2 * padicValNat p (q ^ 5 - 1) := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnd : ¬ p ∣ q := not_dvd_of_orderOf (by norm_num) hord
  have hnq : ¬ p ∣ q ^ 5 := fun h => hnd (hp.dvd_of_dvd_pow h)
  have hd : ∀ d, p ∣ q ^ d - 1 ↔ 5 ∣ d := fun d => dvd_pow_sub_one_iff (by omega) hord
  have hx0 : (q : ZMod p) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff q p).1 h)
  have hdiv : 5 ∣ p - 1 := by
    have h := ZMod.orderOf_dvd_card_sub_one hx0
    rw [hord] at h
    exact h
  have hp6 : p ≠ 6 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have h6 : 6 < p := by omega
  have hne : ∀ d, 0 < d → q ^ d - 1 ≠ 0 := fun d hd0 =>
    Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) hd0.ne')
  have n120 : q ^ 120 ≠ 0 := pow_ne_zero _ (by omega)
  have v120 : padicValNat p (q ^ 120) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (hp.dvd_of_dvd_pow h))
  have v24 : padicValNat p (q ^ 24 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 24).1 h; omega)
  have v18 : padicValNat p (q ^ 18 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 18).1 h; omega)
  have v14 : padicValNat p (q ^ 14 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 14).1 h; omega)
  have v12 : padicValNat p (q ^ 12 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 12).1 h; omega)
  have v8 : padicValNat p (q ^ 8 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 8).1 h; omega)
  have v2 : padicValNat p (q ^ 2 - 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by have := (hd 2).1 h; omega)
  have v30 : padicValNat p (q ^ 30 - 1) = padicValNat p (q ^ 5 - 1) := by
    have h30 : q ^ 30 = q ^ (5 * 6) := by norm_num
    rw [h30]
    exact padicValNat_pow_mul_sub_one hodd hq (by norm_num) ((hd 5).2 dvd_rfl) hnq (by norm_num)
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have v20 : padicValNat p (q ^ 20 - 1) = padicValNat p (q ^ 5 - 1) := by
    have h20 : q ^ 20 = q ^ (5 * 4) := by norm_num
    rw [h20]
    exact padicValNat_pow_mul_sub_one hodd hq (by norm_num) ((hd 5).2 dvd_rfl) hnq (by norm_num)
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
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

theorem padicValNat_card_SL_of_orderOf_eq (K : Type*) [Field K] [Fintype K] {n p : ℕ}
    (hp : p.Prime) (hn : 2 ≤ n) (hord : orderOf ((Fintype.card K : ℕ) : ZMod p) = n) :
    padicValNat p (Nat.card (Matrix.SpecialLinearGroup (Fin n) K)) =
      padicValNat p (Fintype.card K ^ n - 1) := by
  have := Fact.mk hp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K with hqdef
  have hnd : ¬ p ∣ q := not_dvd_of_orderOf (by omega) hord
  have hx : (q : ZMod p) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff q p).1 h)
  have nondiv : ∀ k, 0 < k → k < m + 1 → ¬ p ∣ q ^ (m + 1) - q ^ k := by
    intro k hk0 hk h
    have hcast : ((q ^ (m + 1) - q ^ k : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have hle : q ^ k ≤ q ^ (m + 1) := Nat.pow_le_pow_right (by omega) hk.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, sub_eq_zero] at hcast
    have hfac : (q : ZMod p) ^ (m + 1) = (q : ZMod p) ^ k * (q : ZMod p) ^ (m + 1 - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hfac] at hcast
    have hxk : (q : ZMod p) ^ k ≠ 0 := pow_ne_zero _ hx
    have h1 : (q : ZMod p) ^ (m + 1 - k) = 1 :=
      mul_left_cancel₀ hxk (hcast.trans (mul_one _).symm)
    have hdvd : orderOf (q : ZMod p) ∣ m + 1 - k := orderOf_dvd_iff_pow_eq_one.2 h1
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hU : Nat.card Kˣ = q - 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card]
  have hmul : Nat.card (Matrix.SpecialLinearGroup (Fin (m + 1)) K) * (q - 1) =
      ∏ i : Fin (m + 1), (q ^ (m + 1) - q ^ (i : ℕ)) := by
    rw [← hU, Matrix.card_SL_mul_card_units, Matrix.card_GL_field]
  have hfac : ∏ i : Fin (m + 1), (q ^ (m + 1) - q ^ (i : ℕ)) =
      (q ^ (m + 1) - 1) * ∏ i : Fin m, (q ^ (m + 1) - q ^ ((i : ℕ) + 1)) := by
    rw [Fin.prod_univ_succ]
    simp
  have hA : q ^ (m + 1) - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hR : ¬ p ∣ ∏ i : Fin m, (q ^ (m + 1) - q ^ ((i : ℕ) + 1)) := by
    intro h
    obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
    exact nondiv ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega) hi
  have hR0 : ∏ i : Fin m, (q ^ (m + 1) - q ^ ((i : ℕ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ =>
      Nat.sub_ne_zero_of_lt (pow_lt_pow_right₀ (by omega) (by have := i.isLt; omega))
  have hPval : padicValNat p (∏ i : Fin (m + 1), (q ^ (m + 1) - q ^ (i : ℕ))) =
      padicValNat p (q ^ (m + 1) - 1) := by
    rw [hfac, padicValNat.mul hA hR0, padicValNat.eq_zero_of_not_dvd hR, add_zero]
  have hU_val : padicValNat p (q - 1) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd (fun h => ?_)
    have h1 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one, sub_eq_zero] at h1
    rw [h1, orderOf_one] at hord
    omega
  have hne : Nat.card (Matrix.SpecialLinearGroup (Fin (m + 1)) K) * (q - 1) ≠ 0 := by
    rw [hmul]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      Nat.sub_ne_zero_of_lt (pow_lt_pow_right₀ (by omega) (by have := i.isLt; omega))
  obtain ⟨hS0, hU0⟩ := mul_ne_zero_iff.1 hne
  have hv := congrArg (padicValNat p) hmul
  rw [padicValNat.mul hS0 hU0, hPval, hU_val, add_zero] at hv
  exact hv

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
