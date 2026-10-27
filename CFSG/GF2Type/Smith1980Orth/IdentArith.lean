module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star

public section

namespace CFSG.GF2Type.Smith1980Orth

open Finset CFSG.Timmesfeld

@[expose] def sqProd (k : ℕ) : ℕ := ∏ i ∈ Icc 1 k, (2 ^ (2 * i) - 1)

@[expose] def omegaOdd (b : Bool) (m : ℕ) : ℕ :=
  (if b = true then 2 ^ m - 1 else 2 ^ m + 1) * sqProd (m - 1)

theorem odd_two_pow_sub_one_of_pos {j : ℕ} (hj : 1 ≤ j) : Odd (2 ^ j - 1) := by
  have h : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem odd_two_pow_add_one_of_pos {j : ℕ} (hj : 1 ≤ j) : Odd (2 ^ j + 1) := by
  have h : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  rw [Nat.odd_iff]
  omega

theorem odd_sqProd (k : ℕ) : Odd (sqProd k) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i hi =>
    odd_two_pow_sub_one_of_pos (by have := (mem_Icc.1 hi).1; omega)

theorem odd_omegaOdd (b : Bool) {m : ℕ} (hm : 1 ≤ m) : Odd (omegaOdd b m) := by
  refine Odd.mul ?_ (odd_sqProd _)
  cases b
  · exact odd_two_pow_add_one_of_pos hm
  · exact odd_two_pow_sub_one_of_pos hm

theorem odd_prod_two_pow_sub_one (n : ℕ) : Odd (∏ j ∈ Icc 2 n, (2 ^ j - 1)) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun j hj =>
    odd_two_pow_sub_one_of_pos (by have := (mem_Icc.1 hj).1; omega)

theorem odd_three_mul_omegaOdd_mul (b : Bool) {m i : ℕ} (hm : 1 ≤ m) (hi : i % 4 = 3) :
    Odd (3 * omegaOdd b m * i) :=
  (((by decide : Odd 3)).mul (odd_omegaOdd b hm)).mul (by rw [Nat.odd_iff]; omega)

theorem two_pow_mul_odd_inj {a b x y : ℕ} (hx : Odd x) (hy : Odd y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  have key : ∀ {a b x y : ℕ}, Odd x → 2 ^ a * x = 2 ^ b * y → a < b → False := by
    intro a b x y hx h hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : 2 ^ a * x = 2 ^ a * (2 ^ (c + 1) * y) := by rw [h]; ring
    have h3 : x = 2 ^ (c + 1) * y := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have h4 : 2 ∣ x := by
      rw [h3]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero c)) y
    have := Nat.odd_iff.mp hx
    omega
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (key hx h hab).elim
  · subst hab
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩
  · exact (key hy h.symm hab).elim

theorem sqProd_mod_four (k : ℕ) :
    (k % 2 = 0 → sqProd k % 4 = 1) ∧ (k % 2 = 1 → sqProd k % 4 = 3) := by
  induction k with
  | zero => simp [sqProd]
  | succ k ih =>
    have h : sqProd (k + 1) = sqProd k * (2 ^ (2 * (k + 1)) - 1) := by
      unfold sqProd
      rw [Finset.prod_Icc_succ_top (by omega)]
    have h4 : (2 ^ (2 * (k + 1)) - 1) % 4 = 3 := by
      have h5 : 2 ^ (2 * (k + 1)) = 4 * 4 ^ k := by rw [pow_mul]; ring
      have h6 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [h5]
      omega
    rw [h, Nat.mul_mod, h4]
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [ih1 (by omega)]
    · rw [ih0 (by omega)]

private theorem mul_mod_four {x s a c : ℕ} (hx : x % 4 = a) (hs : s % 4 = c) :
    x * s % 4 = a * c % 4 := by
  rw [Nat.mul_mod, hx, hs]

private theorem exists_two_pow_eq_four_mul {m : ℕ} (hm : 2 ≤ m) :
    ∃ t, 1 ≤ t ∧ 2 ^ m = 4 * t := by
  refine ⟨2 ^ (m - 2), Nat.one_le_two_pow, ?_⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

theorem omegaOdd_true_mod_four {m : ℕ} (hm : 2 ≤ m) :
    ((m - 1) % 2 = 0 → omegaOdd true m % 4 = 3) ∧
      ((m - 1) % 2 = 1 → omegaOdd true m % 4 = 1) := by
  obtain ⟨t, ht, h4⟩ := exists_two_pow_eq_four_mul hm
  obtain ⟨hs0, hs1⟩ := sqProd_mod_four (m - 1)
  have hx : (2 ^ m - 1) % 4 = 3 := by rw [h4]; omega
  unfold omegaOdd
  simp only [if_true]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [mul_mod_four hx (hs0 h)]
  · rw [mul_mod_four hx (hs1 h)]

theorem omegaOdd_false_mod_four {m : ℕ} (hm : 2 ≤ m) :
    ((m - 1) % 2 = 0 → omegaOdd false m % 4 = 1) ∧
      ((m - 1) % 2 = 1 → omegaOdd false m % 4 = 3) := by
  obtain ⟨t, ht, h4⟩ := exists_two_pow_eq_four_mul hm
  obtain ⟨hs0, hs1⟩ := sqProd_mod_four (m - 1)
  have hx : (2 ^ m + 1) % 4 = 1 := by rw [h4]; omega
  unfold omegaOdd
  simp only [Bool.false_eq_true, if_false]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [mul_mod_four hx (hs0 h)]
  · rw [mul_mod_four hx (hs1 h)]

theorem cast_sqProd (k : ℕ) : ((sqProd k : ℕ) : ℤ) = ∏ i ∈ Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1) := by
  unfold sqProd
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rfl

theorem cast_omegaOdd (b : Bool) (m : ℕ) {ε : ℤ}
    (hε : (b = true ∧ ε = 1) ∨ (b = false ∧ ε = -1)) :
    ((omegaOdd b m : ℕ) : ℤ) =
      ((2 : ℤ) ^ m - ε) * ∏ i ∈ Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
  unfold omegaOdd
  rw [Nat.cast_mul, cast_sqProd]
  congr 1
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [if_pos rfl, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rfl
  · rw [if_neg (by simp)]
    push_cast
    ring

theorem psp_numeric {m n e : ℕ} (he : e ≤ 1) : (m + 1) * (m + 2) + e ≠ n * n := by
  intro h
  rcases Nat.lt_or_ge n (m + 2) with h1 | h1
  · have h2 : n ≤ m + 1 := by omega
    nlinarith [Nat.mul_le_mul h2 h2]
  · nlinarith [Nat.mul_le_mul h1 h1]

theorem exceptional_numeric {m e v : ℕ} (hm : 3 ≤ m) (he : e ≤ 1)
    (hv : v = 12 ∨ v = 24 ∨ v = 36 ∨ v = 63 ∨ v = 120) : (m + 1) * (m + 2) + e ≠ v := by
  intro h
  have hm' : m < 11 := by
    by_contra hc
    have : 12 * 13 ≤ (m + 1) * (m + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases m <;> omega

theorem small_numeric {m e y c : ℕ} (hm : 3 ≤ m) (hy : 0 < y) (hc : c < 2 ^ 20)
    (h : c = 2 ^ ((m + 1) * (m + 2) + e) * y) : False := by
  have h1 : 20 ≤ (m + 1) * (m + 2) + e := by
    have : 4 * 5 ≤ (m + 1) * (m + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h2 : 2 ^ 20 ≤ 2 ^ ((m + 1) * (m + 2) + e) := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 2 ^ ((m + 1) * (m + 2) + e) ≤ c := by
    rw [h]
    exact Nat.le_mul_of_pos_right _ hy
  omega

theorem pomega_numeric {n m e i : ℕ} {b b' : Bool} (hn : 4 ≤ n) (hm : 3 ≤ m) (he : e ≤ 1)
    (hi : i % 4 = 3)
    (h : 2 ^ (n * (n - 1)) * omegaOdd b' n =
      2 ^ ((m + 1) * (m + 2) + e) * (3 * omegaOdd b m * i)) :
    n = m + 2 ∧ e = 0 ∧ b' = b := by
  obtain ⟨hexp, hU⟩ := two_pow_mul_odd_inj (odd_omegaOdd b' (by omega))
    (odd_three_mul_omegaOdd_mul b (by omega) hi) h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hexp
  have hnm : n' = m + 1 := by
    rcases lt_trichotomy n' (m + 1) with h1 | h1 | h1
    · exfalso
      have h2 : n' ≤ m := by omega
      nlinarith [Nat.mul_le_mul h2 h2]
    · exact h1
    · exfalso
      have h2 : m + 2 ≤ n' := by omega
      nlinarith [Nat.mul_le_mul h2 h2]
  subst hnm
  have he0 : e = 0 := by nlinarith
  refine ⟨rfl, he0, ?_⟩
  have hmod : omegaOdd b' (m + 1 + 1) % 4 = (3 * omegaOdd b m * 3) % 4 := by
    rw [hU]
    exact Nat.ModEq.mul_left _ (show i ≡ 3 [MOD 4] from hi)
  have h1 := omegaOdd_true_mod_four (m := m) (by omega)
  have h2 := omegaOdd_false_mod_four (m := m) (by omega)
  have h3 := omegaOdd_true_mod_four (m := m + 2) (by omega)
  have h4 := omegaOdd_false_mod_four (m := m + 2) (by omega)
  have e1 : m + 1 + 1 = m + 2 := rfl
  rw [e1] at hmod
  have e2 : m + 2 - 1 = m + 1 := rfl
  rw [e2] at h3 h4
  cases b <;> cases b' <;> simp only at * <;> omega

private theorem two_mul_le_of_dvd {n m i : ℕ} {b : Bool} (hm : 3 ≤ m) (hm4 : m ≠ 4)
    (hprod : ∏ j ∈ Icc 2 n, (2 ^ j - 1) = 3 * omegaOdd b m * i) : 2 * m - 2 ≤ n := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * m - 2) (by omega) (by omega)
  have hk : 0 < 2 * m - 2 := by omega
  have hmem : m - 1 ∈ Icc 1 (m - 1) := mem_Icc.2 ⟨by omega, le_rfl⟩
  have h1 : p ∣ sqProd (m - 1) := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => 2 ^ (2 * i) - 1) hmem)
    have : 2 * (m - 1) = 2 * m - 2 := by omega
    simpa only [this] using hp.dvd
  have h2 : p ∣ ∏ j ∈ Icc 2 n, (2 ^ j - 1) := by
    rw [hprod]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    exact Dvd.dvd.mul_left h1 _
  obtain ⟨j, hj, hpj⟩ := (Nat.Prime.prime hp.prime).dvd_finset_prod_iff _ |>.1 h2
  have hj' := mem_Icc.1 hj
  have := Nat.le_of_dvd (by omega) ((hp.dvd_sub_one_iff hk j).1 hpj)
  omega

private theorem psl_candidates {n m e : ℕ} (hm : 3 ≤ m) (hm4 : m ≠ 4) (he : e ≤ 1)
    (hmn : 2 * m - 2 ≤ n) (hnn : n * (n - 1) = 2 * ((m + 1) * (m + 2) + e)) :
    (m = 3 ∧ n = 7 ∧ e = 1) ∨ (m = 8 ∧ n = 14 ∧ e = 1) := by
  have hn1 : 1 ≤ n := by omega
  have hm8 : m ≤ 8 := by
    by_contra hc
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hnn
    have h2 : 2 * m - 2 ≤ n' + 1 := hmn
    have h3 : 2 * m ≤ n' + 3 := by omega
    nlinarith [Nat.mul_le_mul h3 h3]
  have hn14 : n ≤ 14 := by
    by_contra hc
    have h1 : (m + 1) * (m + 2) ≤ 9 * 10 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 15 * 14 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases m <;> interval_cases n <;> omega

theorem psl_numeric {n m e i : ℕ} {b : Bool} (hn : 3 ≤ n) (hm : 3 ≤ m) (he : e ≤ 1)
    (hi : i % 4 = 3)
    (h : 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (2 ^ j - 1) =
      2 ^ ((m + 1) * (m + 2) + e) * (3 * omegaOdd b m * i)) : False := by
  obtain ⟨hexp, hprod⟩ := two_pow_mul_odd_inj (odd_prod_two_pow_sub_one n)
    (odd_three_mul_omegaOdd_mul b (by omega) hi) h
  have hnn : n * (n - 1) = 2 * ((m + 1) * (m + 2) + e) := by
    have : Even (n * (n - 1)) := Nat.even_mul_pred_self n
    rw [Nat.even_iff] at this
    omega
  by_cases hm4 : m = 4
  · subst hm4
    have hn9 : n < 10 := by
      by_contra hc
      have : 10 * 9 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n <;> omega
  · rcases psl_candidates hm hm4 he (two_mul_le_of_dvd hm hm4 hprod) hnn with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h1 : ∏ j ∈ Icc 2 7, (2 ^ j - 1) = 78129765 := by decide
      have h2 : omegaOdd true 3 = 315 := by decide
      have h3 : omegaOdd false 3 = 405 := by decide
      cases b
      · rw [h1, h3] at hprod
        omega
      · rw [h1, h2] at hprod
        omega
    · have h1 : ∏ j ∈ Icc 2 14, (2 ^ j - 1) = 11715351900195736886933003038875 := by decide
      have h2 : omegaOdd true 8 = 12651918776970598125 := by decide
      have h3 : omegaOdd false 8 = 12751149512476249875 := by decide
      cases b
      · rw [h1, h3] at hprod
        omega
      · rw [h1, h2] at hprod
        omega

end CFSG.GF2Type.Smith1980Orth
