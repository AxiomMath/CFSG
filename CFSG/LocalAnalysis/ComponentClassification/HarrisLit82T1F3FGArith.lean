module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieArith
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG

variable {Q : ℕ}

theorem three_dvd_sq_sub_one (hQ : ¬ 3 ∣ Q) : 3 ∣ Q ^ 2 - 1 := by
  have h0 : Q % 3 ≠ 0 := fun h => hQ (Nat.dvd_of_mod_eq_zero h)
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hQ (dvd_zero 3)
  have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hQ0)
  apply (Nat.modEq_iff_dvd' hQ1).mp
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  have h3 := Nat.mod_lt Q (by norm_num : 3 > 0)
  interval_cases h : Q % 3 <;> simp_all

theorem ordProj_three_sq_pow_sub_one (hQ2 : 2 ≤ Q) (hQ : ¬ 3 ∣ Q) {m : ℕ} (hm : m ≠ 0) :
    ordProj[3] ((Q ^ 2) ^ m - 1) = ordProj[3] (Q ^ 2 - 1) * ordProj[3] m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 < Q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hx : ¬ 3 ∣ Q ^ 2 := fun h => hQ (Nat.prime_three.dvd_of_dvd_pow h)
  have h := padicValNat.pow_sub_pow (p := 3) (x := Q ^ 2) (y := 1) (by decide) h1
    (three_dvd_sq_sub_one hQ) hx hm
  rw [one_pow] at h
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three,
    Nat.factorization_def _ Nat.prime_three, h, pow_add]

theorem ordProj_three_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    ordProj[3] a ≤ ordProj[3] b := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact hb (Nat.eq_zero_of_zero_dvd h)
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.factorization_le_iff_dvd ha hb).mpr h 3)

theorem sq_pow_sub_one_eq (Q e : ℕ) : (Q ^ 2) ^ e - 1 = (Q ^ e + 1) * (Q ^ e - 1) := by
  have h1 : (Q ^ 2) ^ e = (Q ^ e) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have h2 := Nat.sq_sub_sq (Q ^ e) 1
  rw [one_pow] at h2
  rw [h1, h2]

theorem ordProj_three_le_of_dvd_sq_pow (hQ2 : 2 ≤ Q) (hQ : ¬ 3 ∣ Q) {e F : ℕ} (he : e ≠ 0)
    (hdvd : F ∣ (Q ^ 2) ^ e - 1) :
    ordProj[3] F ≤ ordProj[3] (Q ^ 2 - 1) * ordProj[3] e := by
  rw [← ordProj_three_sq_pow_sub_one hQ2 hQ he]
  refine ordProj_three_le_of_dvd ?_ hdvd
  have : 1 < (Q ^ 2) ^ e := Nat.one_lt_pow he (Nat.one_lt_pow (by norm_num) (by omega))
  omega

theorem pow_sub_one_dvd (Q e : ℕ) : Q ^ e - 1 ∣ (Q ^ 2) ^ e - 1 := by
  rw [sq_pow_sub_one_eq]
  exact Dvd.intro_left _ rfl

theorem pow_add_one_dvd (Q e : ℕ) : Q ^ e + 1 ∣ (Q ^ 2) ^ e - 1 := by
  rw [sq_pow_sub_one_eq]
  exact Dvd.intro _ rfl

theorem triality_dvd (Q : ℕ) : Q ^ 8 + Q ^ 4 + 1 ∣ (Q ^ 2) ^ 6 - 1 := by
  refine ⟨Q ^ 4 - 1, ?_⟩
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
  have h12 : 1 ≤ (Q ^ 2) ^ 6 := Nat.one_le_pow _ _ (pow_pos hQ 2)
  zify [h4, h12]
  ring

theorem two_mul_ordProj_three_le (hQ2 : 2 ≤ Q) (hQo : Odd Q) :
    2 * ordProj[3] (Q ^ 2 - 1) ≤ Q + 1 := by
  have h : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    have h2 := Nat.sq_sub_sq Q 1
    rw [one_pow] at h2
    rw [h2, mul_comm]
  have h1 : Q - 1 ≠ 0 := by omega
  have h2 : Q + 1 ≠ 0 := by omega
  rw [h, Nat.ordProj_mul 3 h1 h2]
  by_cases hd : 3 ∣ Q - 1
  · have hn : ¬ 3 ∣ Q + 1 := fun h' =>
      RowLie.false_of_dvd_sub_of_dvd_add Nat.prime_three (by norm_num) (by omega) hd h'
    rw [RowLie.ordProj_eq_one_of_not_dvd hn, mul_one]
    have := RowLie.two_mul_ordProj_le Nat.prime_three (by norm_num) h1
      (Nat.Odd.sub_odd hQo odd_one).two_dvd
    omega
  · rw [RowLie.ordProj_eq_one_of_not_dvd hd, one_mul]
    exact RowLie.two_mul_ordProj_le Nat.prime_three (by norm_num) h2 (hQo.add_odd odd_one).two_dvd

theorem two_mul_cube_le_five_pow {e : ℕ} (he : 4 ≤ e) : 2 * e ^ 3 ≤ 5 ^ (2 * e - 4) := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 2 * (n + 1) - 4 = (2 * n - 4) + 2 := by omega
    rw [h1, pow_add]
    have h2 : (n + 1) ^ 3 ≤ 8 * n ^ 3 := by
      have : n + 1 ≤ 2 * n := by omega
      calc (n + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left this 3
        _ = 8 * n ^ 3 := by ring
    nlinarith

theorem cube_mul_le (hQ : 5 ≤ Q) {c e : ℕ} (he : 2 ≤ e) (hc : c ≤ e) (hc2 : e = 2 → c = 1) :
    c ^ 3 * (Q + 1) ^ 3 ≤ 2 * (Q ^ (e - 1) * (Q ^ e - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 5 := ⟨Q - 5, by omega⟩
  rcases (show e = 2 ∨ e = 3 ∨ 4 ≤ e by omega) with rfl | rfl | he4
  · rw [hc2 rfl]
    have h : (t + 5) ^ 2 - 1 = t ^ 2 + 10 * t + 24 := by
      have : (t + 5) ^ 2 = t ^ 2 + 10 * t + 24 + 1 := by ring
      omega
    rw [h]
    norm_num
    nlinarith [sq_nonneg t]
  · have h : (t + 5) ^ 3 - 1 = t ^ 3 + 15 * t ^ 2 + 75 * t + 124 := by
      have : (t + 5) ^ 3 = t ^ 3 + 15 * t ^ 2 + 75 * t + 124 + 1 := by ring
      omega
    have hc3 : c ^ 3 ≤ 27 := by
      calc c ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hc 3
        _ = 27 := by norm_num
    rw [h]
    norm_num
    nlinarith [sq_nonneg t, pow_nonneg (Nat.zero_le t) 3, pow_nonneg (Nat.zero_le t) 4,
      pow_nonneg (Nat.zero_le t) 5, Nat.mul_le_mul_right ((t + 6) ^ 3) hc3]
  · set Q := t + 5 with hQdef
    have hQ5 : 5 ≤ Q := by omega
    have hQ1 : (Q + 1) ^ 3 ≤ 2 * Q ^ 3 := by
      rw [hQdef]
      nlinarith [sq_nonneg t, pow_nonneg (Nat.zero_le t) 3]
    have hpow : 2 ≤ Q ^ e := le_trans (by omega) (Nat.le_self_pow (by omega) Q)
    have hsub : Q ^ e ≤ 2 * (Q ^ e - 1) := by omega
    have h5 : 5 ^ (2 * e - 4) ≤ Q ^ (2 * e - 4) := Nat.pow_le_pow_left hQ5 _
    have hce : c ^ 3 ≤ e ^ 3 := Nat.pow_le_pow_left hc 3
    have hexp : Q ^ (e - 1) * Q ^ e = Q ^ 3 * Q ^ (2 * e - 4) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc c ^ 3 * (Q + 1) ^ 3 ≤ e ^ 3 * (2 * Q ^ 3) := Nat.mul_le_mul hce hQ1
      _ = Q ^ 3 * (2 * e ^ 3) := by ring
      _ ≤ Q ^ 3 * Q ^ (2 * e - 4) :=
          Nat.mul_le_mul_left _ ((two_mul_cube_le_five_pow he4).trans h5)
      _ = Q ^ (e - 1) * Q ^ e := hexp.symm
      _ ≤ Q ^ (e - 1) * (2 * (Q ^ e - 1)) := Nat.mul_le_mul_left _ hsub
      _ = 2 * (Q ^ (e - 1) * (Q ^ e - 1)) := by ring

theorem four_mul_cube_le (hQ : 5 ≤ Q) {A c e : ℕ} (hA : 2 * A ≤ Q + 1) (he : 2 ≤ e)
    (hc : c ≤ e) (hc2 : e = 2 → c = 1) :
    4 * (A * c) ^ 3 ≤ Q ^ (e - 1) * (Q ^ e - 1) := by
  have h1 : (2 * A) ^ 3 ≤ (Q + 1) ^ 3 := Nat.pow_le_pow_left hA 3
  have h2 := cube_mul_le hQ he hc hc2
  have h8 : 8 * (4 * (A * c) ^ 3) ≤ 8 * (Q ^ (e - 1) * (Q ^ e - 1)) := by
    calc 8 * (4 * (A * c) ^ 3) = 4 * (c ^ 3 * (2 * A) ^ 3) := by ring
      _ ≤ 4 * (c ^ 3 * (Q + 1) ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ ≤ 4 * (2 * (Q ^ (e - 1) * (Q ^ e - 1))) := Nat.mul_le_mul_left _ h2
      _ = 8 * (Q ^ (e - 1) * (Q ^ e - 1)) := by ring
  omega

@[expose] def Ok (Q a k P : ℕ) : Prop :=
  P ≠ 0 ∧ ∃ C : ℕ, ordProj[3] P ≤ C ∧ 4 ^ k * C ^ 3 ≤ Q ^ a * P

theorem Ok.mul {a₁ k₁ P₁ a₂ k₂ P₂ : ℕ} (h₁ : Ok Q a₁ k₁ P₁) (h₂ : Ok Q a₂ k₂ P₂) :
    Ok Q (a₁ + a₂) (k₁ + k₂) (P₁ * P₂) := by
  obtain ⟨hP₁, C₁, h1, h1'⟩ := h₁
  obtain ⟨hP₂, C₂, h2, h2'⟩ := h₂
  refine ⟨mul_ne_zero hP₁ hP₂, C₁ * C₂, ?_, ?_⟩
  · rw [Nat.ordProj_mul 3 hP₁ hP₂]
    exact Nat.mul_le_mul h1 h2
  · calc 4 ^ (k₁ + k₂) * (C₁ * C₂) ^ 3 = (4 ^ k₁ * C₁ ^ 3) * (4 ^ k₂ * C₂ ^ 3) := by ring
      _ ≤ (Q ^ a₁ * P₁) * (Q ^ a₂ * P₂) := Nat.mul_le_mul h1' h2'
      _ = Q ^ (a₁ + a₂) * (P₁ * P₂) := by ring

theorem ok_factor (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {e F : ℕ} (he : 2 ≤ e)
    (hF : Q ^ e - 1 ≤ F) (hdvd : F ∣ (Q ^ 2) ^ e - 1) : Ok Q (e - 1) 1 F := by
  have hpow : 2 ≤ Q ^ e := le_trans (by omega) (Nat.le_self_pow (by omega) Q)
  refine ⟨by omega, ordProj[3] (Q ^ 2 - 1) * ordProj[3] e,
    ordProj_three_le_of_dvd_sq_pow (by omega) hQ3 (by omega) hdvd, ?_⟩
  have hc2 : e = 2 → ordProj[3] e = 1 := by
    rintro rfl
    exact RowLie.ordProj_eq_one_of_not_dvd (by norm_num)
  rw [pow_one]
  exact (four_mul_cube_le hQ (two_mul_ordProj_three_le (by omega) hQo) he
    (Nat.ordProj_le 3 (by omega)) hc2).trans (Nat.mul_le_mul_left _ hF)

theorem le_of_ok (hQ1 : 1 ≤ Q) (hQ3 : ¬ 3 ∣ Q) {N a k P d : ℕ} (hok : Ok Q a k P)
    (ha : a ≤ N) (hd : d ≤ 4 ^ k) : d * (ordProj[3] (Q ^ N * P)) ^ 3 ≤ Q ^ N * P := by
  obtain ⟨hP, C, hC, hC'⟩ := hok
  have hQN : Q ^ N ≠ 0 := pow_ne_zero _ (by omega)
  have h3N : ¬ 3 ∣ Q ^ N := fun h => hQ3 (Nat.prime_three.dvd_of_dvd_pow h)
  rw [Nat.ordProj_mul 3 hQN hP, RowLie.ordProj_eq_one_of_not_dvd h3N, one_mul]
  calc d * (ordProj[3] P) ^ 3 ≤ 4 ^ k * C ^ 3 :=
        Nat.mul_le_mul hd (Nat.pow_le_pow_left hC 3)
    _ ≤ Q ^ a * P := hC'
    _ ≤ Q ^ N * P := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hQ1 ha)

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
