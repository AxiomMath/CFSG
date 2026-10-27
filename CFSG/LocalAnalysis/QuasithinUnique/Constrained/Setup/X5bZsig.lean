module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open Polynomial

namespace CFSG.QuasithinUnique.Setup.X5

theorem natAbs_cyclotomic_two_le (s : ℕ) :
    ((cyclotomic s ℤ).eval (2 : ℤ)).natAbs ≤ 3 ^ s.totient := by
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = (cyclotomic s ℤ).eval (2 : ℤ) := ⟨_, rfl⟩
  have h1 := cyclotomic_eval_le_add_one_pow_totient (q := (2 : ℝ)) (by norm_num) s
  have h2 : (Int.cast v : ℝ) = (cyclotomic s ℝ).eval (2 : ℝ) := by
    have := cyclotomic.eval_apply (2 : ℤ) s (algebraMap ℤ ℝ)
    rw [hv]
    simpa using this.symm
  have h3 : (0 : ℤ) ≤ v := by rw [hv]; exact cyclotomic_nonneg s (by norm_num)
  rw [← hv]
  have : ((v.natAbs : ℕ) : ℝ) ≤ ((3 ^ s.totient : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg h3, h2]
    push_cast
    norm_num at h1 ⊢
    exact h1
  exact_mod_cast this

theorem natAbs_cyclotomic_two_mul_prime_of_dvd {ℓ n : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ n) :
    ((cyclotomic (n * ℓ) ℤ).eval (2 : ℤ)).natAbs =
      ((cyclotomic n ℤ).eval (2 ^ ℓ : ℤ)).natAbs := by
  have h := congrArg (eval (2 : ℤ)) (cyclotomic_expand_eq_cyclotomic hℓ hd ℤ)
  rw [expand_eval] at h
  rw [← h]

theorem natAbs_cyclotomic_two_mul_prime_of_not_dvd {ℓ n : ℕ} (hℓ : ℓ.Prime) (hd : ¬ ℓ ∣ n) :
    ((cyclotomic (n * ℓ) ℤ).eval (2 : ℤ)).natAbs * ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs =
      ((cyclotomic n ℤ).eval (2 ^ ℓ : ℤ)).natAbs := by
  have h := congrArg (eval (2 : ℤ)) (cyclotomic_expand_eq_cyclotomic_mul hℓ hd ℤ)
  rw [expand_eval, eval_mul] at h
  rw [h, Int.natAbs_mul]

theorem two_pow_sub_one_lt_natAbs {n ℓ : ℕ} (hn : 1 < n) (hℓ : 0 < ℓ) :
    (2 ^ ℓ - 1) ^ n.totient < ((cyclotomic n ℤ).eval (2 ^ ℓ : ℤ)).natAbs := by
  have := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (n := n) (q := 2 ^ ℓ) hn
    (Nat.one_lt_two_pow hℓ.ne').ne'
  simpa using this

theorem lt_natAbs_cyclotomic_two {n ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓn : ℓ ∣ n)
    (h6 : 6 ∣ n) (hn : 12 ≤ n) : ℓ < ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs := by
  obtain ⟨s, rfl⟩ := hℓn
  rw [mul_comm ℓ s] at h6 hn ⊢
  have hs1 : 1 < s := by
    by_contra h
    have hs : s = 0 ∨ s = 1 := by omega
    rcases hs with rfl | rfl
    · omega
    · rw [one_mul] at h6
      have := (Nat.Prime.eq_one_or_self_of_dvd hℓ 6 (by simpa using h6))
      omega
  have hlt : ℓ + 1 < 2 ^ ℓ := by
    have h1 : ℓ - 1 < 2 ^ (ℓ - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  by_cases hd : ℓ ∣ s
  · rw [natAbs_cyclotomic_two_mul_prime_of_dvd hℓ hd]
    have := two_pow_sub_one_lt_natAbs (n := s) (ℓ := ℓ) hs1 (by omega)
    have h2 : 2 ^ ℓ - 1 ≤ (2 ^ ℓ - 1) ^ s.totient :=
      Nat.le_self_pow (Nat.totient_pos.2 (by omega)).ne' _
    omega
  · have hmul := natAbs_cyclotomic_two_mul_prime_of_not_dvd hℓ hd
    have hlow := two_pow_sub_one_lt_natAbs (n := s) (ℓ := ℓ) hs1 (by omega)
    have hup := natAbs_cyclotomic_two_le s
    set A := ((cyclotomic (s * ℓ) ℤ).eval (2 : ℤ)).natAbs with hA
    set k := s.totient with hk
    have hAk : (2 ^ ℓ - 1) ^ k < A * 3 ^ k := by
      calc (2 ^ ℓ - 1) ^ k < _ := hlow
        _ = A * ((cyclotomic s ℤ).eval (2 : ℤ)).natAbs := hmul.symm
        _ ≤ A * 3 ^ k := Nat.mul_le_mul_left _ hup
    by_contra hcon
    push Not at hcon
    have hs3 : 3 ≤ s := by
      by_cases h3 : ℓ = 3
      · subst h3; omega
      · have h2s : 2 ∣ s := by
          rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (dvd_trans (by norm_num : 2 ∣ 6) h6) with h | h
          · exact h
          · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h; omega
        have h3s : 3 ∣ s := by
          rcases (Nat.Prime.dvd_mul Nat.prime_three).1 (dvd_trans (by norm_num : 3 ∣ 6) h6) with h | h
          · exact h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 h).symm h3
        have := Nat.le_of_dvd (by omega) h3s
        omega
    have hk2 : 2 ≤ k := by
      have he : Even k := Nat.totient_even (by omega)
      have hp : 0 < k := Nat.totient_pos.2 (by omega)
      obtain ⟨r, hr⟩ := he
      omega
    have h3k : A * 3 ^ k ≤ ℓ * 3 ^ k := Nat.mul_le_mul_right _ hcon
    by_cases h3 : ℓ = 3
    · subst h3
      have h37 : 3 ^ (k + 1) ≤ 7 ^ k := by
        have h7 : 3 ^ (k - 2) ≤ 7 ^ (k - 2) := Nat.pow_le_pow_left (by norm_num) _
        calc 3 ^ (k + 1) = 3 ^ 3 * 3 ^ (k - 2) := by rw [← pow_add]; congr 1; omega
          _ ≤ 7 ^ 2 * 7 ^ (k - 2) := Nat.mul_le_mul (by norm_num) h7
          _ = 7 ^ k := by rw [← pow_add]; congr 1; omega
      have h8 : (2 ^ 3 - 1 : ℕ) = 7 := by norm_num
      rw [h8] at hAk
      have : 3 * 3 ^ k = 3 ^ (k + 1) := by rw [pow_succ]; ring
      omega
    · have h5 : 5 ≤ ℓ := by
        have : ℓ ≠ 4 := by rintro rfl; norm_num at hℓ
        omega
      have hpow : 3 * 2 ^ (ℓ - 2) ≤ 2 ^ ℓ - 1 := by
        have : 2 ^ ℓ = 4 * 2 ^ (ℓ - 2) := by
          rw [show ℓ = (ℓ - 2) + 2 by omega, pow_add]; simp; ring
        have h1 : 1 ≤ 2 ^ (ℓ - 2) := Nat.one_le_two_pow
        omega
      have hge : 3 ^ k * 2 ^ ((ℓ - 2) * k) ≤ (2 ^ ℓ - 1) ^ k := by
        calc 3 ^ k * 2 ^ ((ℓ - 2) * k) = (3 * 2 ^ (ℓ - 2)) ^ k := by rw [mul_pow, ← pow_mul]
          _ ≤ (2 ^ ℓ - 1) ^ k := Nat.pow_le_pow_left hpow k
      have hbig : ℓ ≤ 2 ^ ((ℓ - 2) * k) := by
        have h1 : ℓ ≤ 2 ^ (ℓ - 2) := by
          have h' : ℓ - 3 < 2 ^ (ℓ - 3) := Nat.lt_two_pow_self
          have : 2 ^ (ℓ - 2) = 2 * 2 ^ (ℓ - 3) := by
            rw [← pow_succ']; congr 1; omega
          omega
        calc ℓ ≤ 2 ^ (ℓ - 2) := h1
          _ ≤ 2 ^ ((ℓ - 2) * k) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      have : 3 ^ k * ℓ ≤ 3 ^ k * 2 ^ ((ℓ - 2) * k) := Nat.mul_le_mul_left _ hbig
      have : (2 ^ ℓ - 1) ^ k < ℓ * 3 ^ k := lt_of_lt_of_le hAk h3k
      nlinarith

open CFSG.SL2MinimalFaithful.Zsigmondy in
theorem exists_prime_orderOf_two_eq_six_mul {f : ℕ} (hf : 2 ≤ f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = 6 * f := by
  obtain ⟨n, hn_def⟩ : ∃ n, n = 6 * f := ⟨_, rfl⟩
  have hn12 : 12 ≤ n := by omega
  have h6 : 6 ∣ n := ⟨f, hn_def⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = ((cyclotomic n ℤ).eval (2 : ℤ)).natAbs := ⟨_, rfl⟩
  have hΦ1 : 1 < Φ := by
    have := sub_one_lt_natAbs_cyclotomic_eval (n := n) (q := 2) (by omega) (by norm_num)
    rw [hΦ]
    simpa using this
  rw [← hn_def]
  by_contra hcon
  push Not at hcon
  have key : ∀ ℓ, ℓ.Prime → ℓ ∣ Φ → ∃ e m, 0 < e ∧ ¬ ℓ ∣ m ∧ n = ℓ ^ e * m ∧
      orderOf ((2 : ℕ) : ZMod ℓ) = m ∧ 0 < m ∧ m ∣ ℓ - 1 ∧ ℓ ≠ 2 := by
    intro ℓ hℓ hℓΦ
    have := Fact.mk hℓ
    obtain ⟨e, m, hm, hnm, hord⟩ := orderOf_eq_of_dvd (a := 2) (n := n) (p := ℓ) (by omega)
      (by rw [hΦ] at hℓΦ; simpa using hℓΦ)
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have h2ne : ((2 : ℕ) : ZMod ℓ) ≠ 0 := by
      intro h0
      have h1 := pow_orderOf_eq_one ((2 : ℕ) : ZMod ℓ)
      rw [hord, h0, zero_pow hm0] at h1
      exact zero_ne_one h1
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact h2ne (ZMod.natCast_self 2)
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [pow_zero, one_mul] at hnm
      subst hnm
      exact absurd (by simpa using hord) (hcon ℓ hℓ hℓ2)
    · exact ⟨e, m, he, hm, hnm, hord, Nat.pos_of_ne_zero hm0,
        hord ▸ ZMod.orderOf_dvd_card_sub_one h2ne, hℓ2⟩
  have hℓ : Φ.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, m, he, hm, hnm, hord, hm0, hmℓ, hℓ2⟩ := key _ hℓ (Nat.minFac_dvd Φ)
  set ℓ := Φ.minFac
  have hℓn : ℓ ∣ n := hnm ▸ dvd_mul_of_dvd_left (dvd_pow_self ℓ he.ne') m
  have huniq : ∀ {q : ℕ}, q.Prime → q ∣ Φ → q = ℓ := by
    intro q hq hqΦ
    obtain ⟨e', m', he', -, hnm', -, hm0', hmq, -⟩ := key q hq hqΦ
    by_contra hqℓ
    have hqm : q ∣ m := by
      have hqn : q ∣ n := hnm' ▸ dvd_mul_of_dvd_left (dvd_pow_self q he'.ne') m'
      rw [hnm] at hqn
      rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow h)) hqℓ
      · exact h
    have hℓm' : ℓ ∣ m' := by
      rw [hnm'] at hℓn
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h)).symm hqℓ
      · exact h
    have h1 : q ≤ m := Nat.le_of_dvd hm0 hqm
    have h2 : m ≤ ℓ - 1 := Nat.le_of_dvd (by have := hℓ.two_le; omega) hmℓ
    have h3 : ℓ ≤ m' := Nat.le_of_dvd hm0' hℓm'
    have h4 : m' ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hmq
    omega
  have := Fact.mk hℓ
  have hv : padicValNat ℓ Φ ≤ 1 := by
    have := padicValNat_le_one (n := n) (p := ℓ) (e := e) (m := m) (a := 2) hℓ2 he hnm hord hm0
      (by norm_num)
    rw [hΦ]
    simpa using this
  have hΦℓ : Φ = ℓ := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : Φ ≠ 0)
      (fun hd hdΦ => huniq hd hdΦ)
    set k := Φ.primeFactorsList.length
    have hk : padicValNat ℓ Φ = k := by rw [hpow]; exact padicValNat.prime_pow k
    have hk1 : k ≤ 1 := hk ▸ hv
    interval_cases k
    · rw [pow_zero] at hpow; omega
    · rwa [pow_one] at hpow
  have hℓ3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega
  have hlt := lt_natAbs_cyclotomic_two hℓ hℓ3 hℓn h6 hn12
  rw [← hΦ] at hlt
  omega

theorem orderOf_two_pow_eq_six {ℓ f : ℕ} (hf : 1 ≤ f) (h : orderOf (2 : ZMod ℓ) = 6 * f) :
    orderOf ((2 ^ f : ℕ) : ZMod ℓ) = 6 := by
  have h1 : ((2 ^ f : ℕ) : ZMod ℓ) = (2 : ZMod ℓ) ^ f := by push_cast; rfl
  rw [h1, orderOf_pow' _ (by omega), h]
  have : Nat.gcd (6 * f) f = f := Nat.gcd_eq_right (dvd_mul_left f 6)
  rw [this]
  exact Nat.mul_div_cancel _ (by omega)

theorem orderOf_and_quad_of_orderOf_two {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f) :
    orderOf ((2 ^ f : ℕ) : ZMod ℓ) = 6 ∧
      ((2 ^ f : ℕ) : ZMod ℓ) ^ 2 - ((2 ^ f : ℕ) : ZMod ℓ) + 1 = 0 := by
  have hq6 := orderOf_two_pow_eq_six hf hord
  obtain ⟨x, hx⟩ : ∃ x : ZMod ℓ, x = ((2 ^ f : ℕ) : ZMod ℓ) := ⟨_, rfl⟩
  rw [← hx] at hq6 ⊢
  refine ⟨hq6, ?_⟩
  have hx6 : x ^ 6 = 1 := by rw [← hq6]; exact pow_orderOf_eq_one x
  have hx3 : x ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq6]; norm_num)
  have hx2 : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq6]; norm_num)
  have hx3' : x ^ 3 = -1 := by
    have : (x ^ 3) * (x ^ 3) = 1 := by rw [← pow_add]; exact hx6
    rcases mul_self_eq_one_iff.mp this with h | h
    · exact absurd h hx3
    · exact h
  have hx1 : x + 1 ≠ 0 := by
    intro h
    have : x = -1 := eq_neg_of_add_eq_zero_left h
    apply hx2
    rw [this]; exact neg_one_sq
  have h3 : x ^ 3 + 1 = 0 := by rw [hx3']; exact neg_add_cancel 1
  have : (x + 1) * (x ^ 2 - x + 1) = 0 := by rw [← h3]; ring
  exact (mul_eq_zero.mp this).resolve_left hx1

theorem binary_multiple_six_exponents_have_primitive_prime_divisors {f : ℕ} (hf : 2 ≤ f) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = 6 * f ∧
      orderOf ((2 ^ f : ℕ) : ZMod ℓ) = 6 ∧ ℓ ∣ (2 ^ f) ^ 2 - 2 ^ f + 1 ∧
      ¬ ℓ ∣ 3 * (2 ^ f + 1) := by
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq_six_mul hf
  have := Fact.mk hℓ
  have hq6 := orderOf_two_pow_eq_six (by omega) hord
  obtain ⟨x, hx⟩ : ∃ x : ZMod ℓ, x = ((2 ^ f : ℕ) : ZMod ℓ) := ⟨_, rfl⟩
  rw [← hx] at hq6
  have hx6 : x ^ 6 = 1 := by rw [← hq6]; exact pow_orderOf_eq_one x
  have hx3 : x ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq6]; norm_num)
  have hx2 : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq6]; norm_num)
  have hx3' : x ^ 3 = -1 := by
    have : (x ^ 3) * (x ^ 3) = 1 := by rw [← pow_add]; exact hx6
    rcases mul_self_eq_one_iff.mp this with h | h
    · exact absurd h hx3
    · exact h
  have hx1 : x + 1 ≠ 0 := by
    intro h
    have : x = -1 := eq_neg_of_add_eq_zero_left h
    apply hx2
    rw [this]; exact neg_one_sq
  have hquad : x ^ 2 - x + 1 = 0 := by
    have h3 : x ^ 3 + 1 = 0 := by rw [hx3']; exact neg_add_cancel 1
    have : (x + 1) * (x ^ 2 - x + 1) = 0 := by rw [← h3]; ring
    exact (mul_eq_zero.mp this).resolve_left hx1
  have hx' : x = (2 : ZMod ℓ) ^ f := by rw [hx]; push_cast; rfl
  have h2ne : (2 : ZMod ℓ) ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one (2 : ZMod ℓ)
    rw [hord, h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  refine ⟨ℓ, hℓ, hℓ2, hord, by rw [← hx]; exact hq6, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]
    have hle : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [Nat.cast_add, Nat.cast_sub hle]
    push_cast
    rw [← hx']
    linear_combination hquad
  · intro hdvd
    rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
    · have h3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h
      have h1 := ZMod.orderOf_dvd_card_sub_one h2ne
      rw [hord, h3] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · apply hx1
      rw [← ZMod.natCast_eq_zero_iff] at h
      rw [hx]
      simpa using h

end CFSG.QuasithinUnique.Setup.X5
