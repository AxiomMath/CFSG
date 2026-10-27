module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClDisp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem not_dvd_414720_of_three_pow_five {n : ℕ} (h5 : 3 ^ 5 ∣ n) : ¬ n ∣ 414720 := fun hn => by
  have := h5.trans hn
  norm_num at this

theorem false_of_bounds_omega {n : ℕ} (h2 : n ∣ 414720) (hgt : 414720 < n) : False := by
  have h3 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem omega_split_cases {a b f : ℕ} (hf : 1 ≤ f) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 7 ≤ a + b) :
    5 ≤ f * ((a - 1) ^ 2 / 4 + (b - 1) ^ 2 / 4) ∨
      (f = 1 ∧ ((a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨
        (a = 4 ∧ b = 4))) := by
  have key : 5 ≤ (a - 1) ^ 2 / 4 + (b - 1) ^ 2 / 4 ∨
      (3 ≤ (a - 1) ^ 2 / 4 + (b - 1) ^ 2 / 4 ∧
        ((a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨
          (a = 4 ∧ b = 4))) := by
    by_cases ha8 : 8 ≤ a
    · left
      have : 12 ≤ (a - 1) ^ 2 / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        obtain ⟨s, rfl⟩ : ∃ s, a = s + 8 := ⟨a - 8, by omega⟩
        rw [show s + 8 - 1 = s + 7 by omega]
        nlinarith
      omega
    by_cases hb8 : 8 ≤ b
    · left
      have : 12 ≤ (b - 1) ^ 2 / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        obtain ⟨s, rfl⟩ : ∃ s, b = s + 8 := ⟨b - 8, by omega⟩
        rw [show s + 8 - 1 = s + 7 by omega]
        nlinarith
      omega
    push Not at ha8 hb8
    interval_cases a <;> interval_cases b <;> omega
  rcases key with h | ⟨h3, hl⟩
  · exact Or.inl (h.trans (Nat.le_mul_of_pos_left _ hf))
  · by_cases hf1 : f = 1
    · exact Or.inr ⟨hf1, hl⟩
    · left
      have hf2 : 2 ≤ f := by omega
      nlinarith

theorem u42_six_le_tri {m : ℕ} (hm : 4 ≤ m) : 6 ≤ m * (m - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 4 := ⟨m - 4, by omega⟩
  rw [show s + 4 - 1 = s + 3 by omega]
  nlinarith

theorem u42_four_le_sq_div {m : ℕ} (hm : 5 ≤ m) : 4 ≤ (m - 1) ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 5 := ⟨m - 5, by omega⟩
  rw [show s + 5 - 1 = s + 4 by omega]
  nlinarith

theorem u42_class_three_numeric {f m : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m) :
    5 ≤ 2 * f * ((m - 1) ^ 2 / 4) ∨ (m = 4 ∧ f = 1) := by
  by_cases hm4 : m = 4
  · subst hm4
    by_cases hf1 : f = 1
    · exact Or.inr ⟨rfl, hf1⟩
    · left
      norm_num
      omega
  · left
    have := u42_four_le_sq_div (show 5 ≤ m by omega)
    nlinarith

theorem u42_class_gl_numeric {f m : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m) :
    5 ≤ f * (m * (m - 1) / 2) := by
  have := u42_six_le_tri hm
  nlinarith

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
