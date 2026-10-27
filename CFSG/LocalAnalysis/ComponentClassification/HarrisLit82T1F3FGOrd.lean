module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGArith
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Assembly.LowTwoRank CatLeaf

variable {Q : ℕ}

theorem Ok.congr {a k P a' k' : ℕ} (h : Ok Q a k P) (ha : a = a') (hk : k = k') :
    Ok Q a' k' P := ha ▸ hk ▸ h

theorem ok_pow_sub (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {e : ℕ} (he : 2 ≤ e) :
    Ok Q (e - 1) 1 (Q ^ e - 1) :=
  ok_factor hQ hQo hQ3 he le_rfl (pow_sub_one_dvd Q e)

theorem ok_pow_add (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {e : ℕ} (he : 2 ≤ e) :
    Ok Q (e - 1) 1 (Q ^ e + 1) :=
  ok_factor hQ hQo hQ3 he (by omega) (pow_add_one_dvd Q e)

theorem ok_psl (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {n : ℕ} (hn : 2 ≤ n) :
    Ok Q (n * (n - 1) / 2) (n - 1) (∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.prod_singleton]
    exact ok_pow_sub hQ hQo hQ3 le_rfl
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    exact (ih.mul (ok_pow_sub hQ hQo hQ3 (by omega : 2 ≤ n + 1))).congr
      (by rw [Nat.triangle_succ]; omega) (by omega)

theorem ok_psu (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {n : ℕ} (hn : 2 ≤ n) :
    Ok Q (n * (n - 1) / 2) (n - 1)
      (∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1)) := by
  have hf : ∀ {e : ℕ}, 2 ≤ e →
      Ok Q (e - 1) 1 (if Even e then Q ^ e - 1 else Q ^ e + 1) := by
    intro e he
    split_ifs
    · exact ok_pow_sub hQ hQo hQ3 he
    · exact ok_pow_add hQ hQo hQ3 he
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.prod_singleton]
    exact hf le_rfl
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    exact (ih.mul (hf (by omega : 2 ≤ n + 1))).congr (by rw [Nat.triangle_succ]; omega)
      (by omega)

theorem ok_psp (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {n : ℕ} (hn : 1 ≤ n) :
    Ok Q (n ^ 2) n (∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.prod_singleton]
    exact (ok_pow_sub hQ hQo hQ3 (by norm_num : 2 ≤ 2 * 1)).congr (by norm_num) rfl
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    exact (ih.mul (ok_pow_sub hQ hQo hQ3 (by omega : 2 ≤ 2 * (n + 1)))).congr
      (by
        have : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [this]
        ring)
      rfl

theorem ok_omega (hQ : 5 ≤ Q) (hQo : Odd Q) (hQ3 : ¬ 3 ∣ Q) {n c : ℕ} (hn : 2 ≤ n)
    (hc : Ok Q (n - 1) 1 c) :
    Ok Q (n * (n - 1)) n (c * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  exact (hc.mul (ok_psp hQ hQo hQ3 (by omega : 1 ≤ m))).congr (by ring) (by ring)

theorem le_four_pow_pred {n : ℕ} (hn : 1 ≤ n) : n ≤ 4 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.add_sub_cancel, show n = (n - 1) + 1 by omega, pow_succ]
    omega

theorem divisor_mul_ordProj_three_pow_le {τ : StatedLieTag} {n r f : ℕ}
    (hadm : StatedLieAdmissible τ n r f) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    lieOrderDivisor τ n (r ^ f) * (ordProj[3] (lieOrderNumerator τ n (r ^ f))) ^ 3 ≤
      lieOrderNumerator τ n (r ^ f) := by
  obtain ⟨hr, hf, hcase⟩ := hadm
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by decide)
    omega
  have hQ : 5 ≤ r ^ f := hr5.trans (Nat.le_self_pow (by omega) r)
  have hQo : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
  have hQ3 : ¬ 3 ∣ r ^ f := fun h =>
    hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  generalize r ^ f = Q at hQ hQo hQ3 ⊢
  have hQ1 : 1 ≤ Q := by omega
  have sub := fun {e : ℕ} (he : 2 ≤ e) => ok_pow_sub hQ hQo hQ3 he
  have add := fun {e : ℕ} (he : 2 ≤ e) => ok_pow_add hQ hQo hQ3 he
  cases τ with
  | PSL =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    obtain ⟨hn, -, -⟩ := hcase
    exact le_of_ok hQ1 hQ3 (ok_psl hQ hQo hQ3 hn) le_rfl
      ((Nat.gcd_le_left _ (by omega)).trans (le_four_pow_pred (by omega)))
  | PSU =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    obtain ⟨hn, -⟩ := hcase
    exact le_of_ok hQ1 hQ3 (ok_psu hQ hQo hQ3 (by omega)) le_rfl
      ((Nat.gcd_le_left _ (by omega)).trans (le_four_pow_pred (by omega)))
  | PSp =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    obtain ⟨hn, -⟩ := hcase
    exact le_of_ok hQ1 hQ3 (ok_psp hQ hQo hQ3 (by omega)) le_rfl
      ((Nat.gcd_le_left _ (by norm_num)).trans
        (by calc 2 ≤ 4 ^ 1 := by norm_num
              _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)))
  | POmegaOdd =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    obtain ⟨hn, -⟩ := hcase
    exact le_of_ok hQ1 hQ3 (ok_psp hQ hQo hQ3 (by omega)) le_rfl
      (by calc 2 ≤ 4 ^ 1 := by norm_num
            _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
  | POmegaPlus =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [mul_assoc]
    exact le_of_ok hQ1 hQ3 (ok_omega hQ hQo hQ3 (by omega) (sub (by omega))) le_rfl
      ((Nat.gcd_le_left _ (by norm_num)).trans
        (by calc 4 = 4 ^ 1 := by norm_num
              _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)))
  | POmegaMinus =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [mul_assoc]
    exact le_of_ok hQ1 hQ3 (ok_omega hQ hQo hQ3 (by omega) (add (by omega))) le_rfl
      ((Nat.gcd_le_left _ (by norm_num)).trans
        (by calc 4 = 4 ^ 1 := by norm_num
              _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)))
  | G2 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [mul_assoc]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 6)).mul (sub le_rfl)) (by norm_num)
      (by norm_num)
  | F4 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d e : ℕ, a * b * c * d * e = a * (b * (c * (d * e))) by intros; ring]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 12)).mul ((sub (by norm_num : 2 ≤ 8)).mul
      ((sub (by norm_num : 2 ≤ 6)).mul (sub le_rfl)))) (by norm_num) (by norm_num)
  | E6 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d e g h : ℕ, a * b * c * d * e * g * h =
      a * (b * (c * (d * (e * (g * h))))) by intros; ring]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 12)).mul ((sub (by norm_num : 2 ≤ 9)).mul
      ((sub (by norm_num : 2 ≤ 8)).mul ((sub (by norm_num : 2 ≤ 6)).mul
      ((sub (by norm_num : 2 ≤ 5)).mul (sub le_rfl)))))) (by norm_num)
      ((Nat.gcd_le_left _ (by norm_num)).trans (by norm_num))
  | E7 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d e g h i : ℕ, a * b * c * d * e * g * h * i =
      a * (b * (c * (d * (e * (g * (h * i)))))) by intros; ring]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 18)).mul ((sub (by norm_num : 2 ≤ 14)).mul
      ((sub (by norm_num : 2 ≤ 12)).mul ((sub (by norm_num : 2 ≤ 10)).mul
      ((sub (by norm_num : 2 ≤ 8)).mul ((sub (by norm_num : 2 ≤ 6)).mul (sub le_rfl)))))))
      (by norm_num) ((Nat.gcd_le_left _ (by norm_num)).trans (by norm_num))
  | E8 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d e g h i j : ℕ, a * b * c * d * e * g * h * i * j =
      a * (b * (c * (d * (e * (g * (h * (i * j))))))) by intros; ring]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 30)).mul ((sub (by norm_num : 2 ≤ 24)).mul
      ((sub (by norm_num : 2 ≤ 20)).mul ((sub (by norm_num : 2 ≤ 18)).mul
      ((sub (by norm_num : 2 ≤ 14)).mul ((sub (by norm_num : 2 ≤ 12)).mul
      ((sub (by norm_num : 2 ≤ 8)).mul (sub le_rfl)))))))) (by norm_num) (by norm_num)
  | twistedE6 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d e g h : ℕ, a * b * c * d * e * g * h =
      a * (b * (c * (d * (e * (g * h))))) by intros; ring]
    exact le_of_ok hQ1 hQ3 ((sub (by norm_num : 2 ≤ 12)).mul ((add (by norm_num : 2 ≤ 9)).mul
      ((sub (by norm_num : 2 ≤ 8)).mul ((sub (by norm_num : 2 ≤ 6)).mul
      ((add (by norm_num : 2 ≤ 5)).mul (sub le_rfl)))))) (by norm_num)
      ((Nat.gcd_le_left _ (by norm_num)).trans (by norm_num))
  | trialityD4 =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    rw [show ∀ a b c d : ℕ, a * b * c * d = a * (b * (c * d)) by intros; ring]
    have h3 : Ok Q (6 - 1) 1 (Q ^ 8 + Q ^ 4 + 1) := ok_factor hQ hQo hQ3 (by norm_num)
      ((Nat.sub_le _ _).trans (by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ Q) (by norm_num : 6 ≤ 8)
        omega)) (triality_dvd Q)
    exact le_of_ok hQ1 hQ3 (h3.mul ((sub (by norm_num : 2 ≤ 6)).mul (sub le_rfl)))
      (by norm_num) (by norm_num)
  | twistedB2 => exact absurd hcase.2.1 hr2
  | twistedG2 => exact absurd hcase.2.1 hr3
  | twistedF4 => exact absurd hcase.2.1 hr2
  | Tits => exact absurd hcase.2.1 hr2

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
