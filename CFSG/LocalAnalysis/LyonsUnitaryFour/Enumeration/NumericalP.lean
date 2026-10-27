module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Reciprocal
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LyonsUnitaryFour

private theorem not_inv_eq_of_not_dvd {x : ℤ} {a b : ℤ} (hb : b ≠ 0) (hdvd : ¬ b ∣ a)
    (h : (x : ℚ)⁻¹ = b / a) : False := by
  have ha : (a : ℚ) ≠ 0 := by
    have : a ≠ 0 := fun h0 => hdvd (h0 ▸ dvd_zero b)
    exact_mod_cast this
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hx : (x : ℚ) ≠ 0 := by
    intro hx
    rw [hx, inv_zero] at h
    exact div_ne_zero hb' ha h.symm
  have : (x : ℚ) * b = a := by
    rw [eq_div_iff ha] at h
    rw [← h, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  have h' : x * b = a := by exact_mod_cast this
  exact hdvd ⟨x, by rw [← h', mul_comm]⟩

theorem lyons_configuration_P_numerical_impossibility (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℤ)
    (h₁ : 12 ≤ |x₁|) (h₂ : 12 ≤ |x₂|) (_h₃ : 12 ≤ |x₃|) (_h₄ : 12 ≤ |x₄|) (_h₅ : 12 ≤ |x₅|)
    (h₆ : 12 ≤ |x₆|) (_h₇ : 12 ≤ |x₇|) (_h₈ : 12 ≤ |x₈|) (_h₉ : 12 ≤ |x₉|) (_h₁₀ : 12 ≤ |x₁₀|)
    (c₁ : x₁ ≡ 1 [ZMOD 64]) (c₂ : x₂ ≡ 1 [ZMOD 64]) (c₆ : x₆ ≡ 1 [ZMOD 64])
    (c₃ : x₃ ≡ 52 [ZMOD 64]) (c₄ : x₄ ≡ 52 [ZMOD 64]) (c₉ : x₉ ≡ 52 [ZMOD 64])
    (c₁₀ : x₁₀ ≡ 52 [ZMOD 64]) (c₅ : x₅ ≡ 26 [ZMOD 64]) (c₇ : x₇ ≡ 53 [ZMOD 64])
    (c₈ : x₈ ≡ 53 [ZMOD 64])
    (p₅ : 0 < x₅ → 90 ≤ x₅) (n₇ : x₇ < 0 → x₇ ≤ -75) (n₈ : x₈ < 0 → x₈ ≤ -75)
    (e₁ : (1 : ℚ) + 4 / x₁ + 4 / x₂ - 200 / x₅ + 1 / x₆ + 25 / x₇ + 25 / x₈ = 0)
    (e₂ : (1 : ℚ) - 1 / x₁ - 1 / x₂ + 16 / x₃ + 16 / x₄ + 1 / x₆ - 16 / x₉ - 16 / x₁₀ = 0)
    (e₃ : 0 < -(4 : ℚ) / x₁ - 4 / x₂ + 64 / x₃ + 64 / x₄ + 400 / x₅) : False := by
  simp only [Int.ModEq] at c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀
  have b₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ h₁; rw [le_abs'] at h₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ h₂; rw [le_abs'] at h₂; omega)
  have b₆ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₆)
    (by clear * - c₆ h₆; rw [le_abs'] at h₆; omega)
  have b₇ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := x₇)
    (by rcases lt_or_ge x₇ 0 with h | h
        · exact Or.inr (n₇ h)
        · left; clear * - c₇ h; omega)
  have b₈ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := x₈)
    (by rcases lt_or_ge x₈ 0 with h | h
        · exact Or.inr (n₈ h)
        · left; clear * - c₈ h; omega)
  have b₃ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃; omega)
  have b₄ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := x₄)
    (by clear * - c₄; omega)
  have b₉ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := x₉)
    (by clear * - c₉; omega)
  have b₁₀ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := x₁₀)
    (by clear * - c₁₀; omega)
  push_cast at b₁ b₂ b₃ b₄ b₆ b₇ b₈ b₉ b₁₀
  simp only [div_eq_mul_inv] at e₁ e₂ e₃
  have hx₅pos : 0 < x₅ := by
    have : (0 : ℚ) < (x₅ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1, b₆.1, b₇.1, b₈.1]
    have : (0 : ℚ) < x₅ := inv_pos.mp this
    exact_mod_cast this
  have hx₅90 := p₅ hx₅pos
  have hx₅ : 154 ≤ x₅ := by
    by_contra hlt
    have h90 : x₅ = 90 := by clear * - hx₅90 hlt c₅; omega
    rw [h90] at e₁
    push_cast at e₁
    linarith [b₁.2, b₂.2, b₆.2, b₇.2, b₈.2]
  have b₅ := inv_pos_le_of_le (A := 154) (by norm_num) hx₅
  push_cast at b₅
  have n₃ : x₃ ≠ -12 := by
    intro h
    rw [h] at e₃
    push_cast at e₃
    linarith [b₁.1, b₂.1, b₄.2, b₅.2]
  have n₄ : x₄ ≠ -12 := by
    intro h
    rw [h] at e₃
    push_cast at e₃
    linarith [b₁.1, b₂.1, b₃.2, b₅.2]
  have b₃' := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃ n₃; omega)
  have b₄' := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := x₄)
    (by clear * - c₄ n₄; omega)
  push_cast at b₃' b₄'
  have hx₃ : x₃ = -76 := by
    by_contra hne
    have := inv_mem_of_le_or_le (A := 52) (B := 140) (by norm_num) (by norm_num) (x := x₃)
      (by clear * - c₃ n₃ hne; omega)
    push_cast at this
    linarith [this.1, b₄'.1, b₉.2, b₁₀.2, b₁.2, b₂.2, b₆.1]
  have hx₄ : x₄ = -76 := by
    by_contra hne
    have := inv_mem_of_le_or_le (A := 52) (B := 140) (by norm_num) (by norm_num) (x := x₄)
      (by clear * - c₄ n₄ hne; omega)
    push_cast at this
    linarith [this.1, b₃'.1, b₉.2, b₁₀.2, b₁.2, b₂.2, b₆.1]
  rw [hx₃, hx₄] at e₂
  push_cast at e₂
  have hx₉ : x₉ = 52 := by
    by_contra hne
    have := inv_mem_of_le_or_le (A := 116) (B := 12) (by norm_num) (by norm_num) (x := x₉)
      (by clear * - c₉ hne; omega)
    push_cast at this
    linarith [this.2, b₁₀.2, b₁.2, b₂.2, b₆.1]
  have hx₁₀ : x₁₀ = 52 := by
    by_contra hne
    have := inv_mem_of_le_or_le (A := 116) (B := 12) (by norm_num) (by norm_num) (x := x₁₀)
      (by clear * - c₁₀ hne; omega)
    push_cast at this
    linarith [this.2, b₉.2, b₁.2, b₂.2, b₆.1]
  rw [hx₉, hx₁₀] at e₂
  push_cast at e₂
  have hA : (x₁ : ℚ)⁻¹ + (x₂ : ℚ)⁻¹ - (x₆ : ℚ)⁻¹ = -(9 / 247) := by linarith
  have far₁ : x₁ ≠ -63 → -(1 / 127 : ℚ) ≤ (x₁ : ℚ)⁻¹ := fun hne => by
    have := inv_mem_of_le_or_le (A := 65) (B := 127) (by norm_num) (by norm_num) (x := x₁)
      (by clear * - c₁ h₁ hne; rw [le_abs'] at h₁; omega)
    push_cast at this
    exact this.1
  have far₂ : x₂ ≠ -63 → -(1 / 127 : ℚ) ≤ (x₂ : ℚ)⁻¹ := fun hne => by
    have := inv_mem_of_le_or_le (A := 65) (B := 127) (by norm_num) (by norm_num) (x := x₂)
      (by clear * - c₂ h₂ hne; rw [le_abs'] at h₂; omega)
    push_cast at this
    exact this.1
  have far₆ : x₆ ≠ 65 → (x₆ : ℚ)⁻¹ ≤ 1 / 129 := fun hne => by
    have := inv_mem_of_le_or_le (A := 129) (B := 63) (by norm_num) (by norm_num) (x := x₆)
      (by clear * - c₆ h₆ hne; rw [le_abs'] at h₆; omega)
    push_cast at this
    exact this.2
  by_cases m₁ : x₁ = -63
  · by_cases m₂ : x₂ = -63
    · rw [m₁, m₂] at hA
      push_cast at hA
      exact not_inv_eq_of_not_dvd (x := x₆) (a := 15561) (b := 73) (by norm_num) (by decide)
        (by push_cast; linarith)
    · by_cases m₆ : x₆ = 65
      · rw [m₁, m₆] at hA
        push_cast at hA
        exact not_inv_eq_of_not_dvd (x := x₂) (a := 5985) (b := -31) (by norm_num) (by decide)
          (by push_cast; linarith)
      · rw [m₁] at hA
        push_cast at hA
        linarith [far₂ m₂, far₆ m₆]
  · by_cases m₂ : x₂ = -63
    · by_cases m₆ : x₆ = 65
      · rw [m₂, m₆] at hA
        push_cast at hA
        exact not_inv_eq_of_not_dvd (x := x₁) (a := 5985) (b := -31) (by norm_num) (by decide)
          (by push_cast; linarith)
      · rw [m₂] at hA
        push_cast at hA
        linarith [far₁ m₁, far₆ m₆]
    · linarith [far₁ m₁, far₂ m₂, b₆.2]

end CFSG.LyonsUnitaryFour
