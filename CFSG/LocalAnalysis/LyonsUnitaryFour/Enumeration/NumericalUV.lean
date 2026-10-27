module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Reciprocal
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LyonsUnitaryFour

theorem lyons_second_reciprocal_small_fourth_degree (x₁ x₂ x₃ x₄ x₆ x₇ : ℤ)
    (_h₁ : 12 ≤ |x₁|) (_h₂ : 12 ≤ |x₂|) (h₃ : 12 ≤ |x₃|) (_h₄ : 12 ≤ |x₄|) (h₆ : 12 ≤ |x₆|)
    (_h₇ : 12 ≤ |x₇|)
    (c₁ : x₁ ≡ 51 [ZMOD 64]) (c₂ : x₂ ≡ 52 [ZMOD 64]) (c₇ : x₇ ≡ 52 [ZMOD 64])
    (c₃ : x₃ ≡ 1 [ZMOD 64]) (c₆ : x₆ ≡ 1 [ZMOD 64]) (c₄ : x₄ ≡ 39 [ZMOD 64])
    (n₁ : x₁ ≠ -13) (n₂ : x₂ ≠ -12)
    (hp : ∀ p : ℕ, p.Prime → p ∣ x₄.natAbs →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1 ∧ (p : ℤ) ≤ |x₃| + 1 ∧ (p : ℤ) ≤ |x₇| + 1)
    (heq : (1 : ℚ) + 18 / x₁ + 16 / x₂ - 1 / x₃ - 49 / x₄ + 1 / x₆ - 16 / x₇ = 0) :
    x₄ = 39 := by
  simp only [Int.ModEq] at c₁ c₂ c₃ c₄ c₆ c₇
  have b₁ := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ n₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ n₂; omega)
  have b₃ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃ h₃; rw [le_abs'] at h₃; omega)
  have b₆ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₆)
    (by clear * - c₆ h₆; rw [le_abs'] at h₆; omega)
  have b₇ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := x₇)
    (by clear * - c₇; omega)
  push_cast at b₁ b₂ b₃ b₆ b₇
  simp only [div_eq_mul_inv] at heq
  have hlow : (1 / 228 : ℚ) < (x₄ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1, b₃.2, b₆.1, b₇.2]
  obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hlt' : x₄ < 228 := by
    have : (x₄ : ℚ) < 228 := by norm_num at hlt; exact hlt
    exact_mod_cast this
  have hcases : x₄ = 39 ∨ x₄ = 103 ∨ x₄ = 167 := by clear * - hpos hlt' c₄; omega
  have big : ∀ p : ℕ, p.Prime → x₄ = p → (49 : ℚ) / p < 1 - 51 / (p - 1) - 1 / 63 → False := by
    intro p hpp hx hlt
    obtain ⟨p₁, p₂, p₃, p₇⟩ := hp p hpp (by rw [hx]; simp)
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hpp.two_le
    have key : ∀ x : ℤ, (p : ℤ) ≤ |x| + 1 →
        -(1 / ((p : ℚ) - 1)) ≤ (x : ℚ)⁻¹ ∧ (x : ℚ)⁻¹ ≤ 1 / ((p : ℚ) - 1) := by
      intro x hx
      have := inv_mem_of_le_or_le (A := p - 1) (B := p - 1) (by omega) (by omega) (x := x)
        (by rcases le_abs'.mp (by linarith : (p : ℤ) - 1 ≤ |x|) with h | h <;> omega)
      push_cast at this
      exact this
    have e₁ := key x₁ p₁
    have e₂ := key x₂ p₂
    have e₃ := key x₃ p₃
    have e₇ := key x₇ p₇
    have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
      have : (2 : ℚ) ≤ p := by exact_mod_cast hpp.two_le
      linarith
    rw [hx] at heq
    simp only [div_eq_mul_inv] at hlt
    have hpinv : ((p : ℤ) : ℚ)⁻¹ = (p : ℚ)⁻¹ := by norm_cast
    rw [hpinv] at heq
    have : (1 / ((p : ℚ) - 1)) = ((p : ℚ) - 1)⁻¹ := one_div _
    rw [this] at e₁ e₂ e₃ e₇
    nlinarith [e₁.1, e₂.1, e₃.2, e₇.2, b₆.1]
  rcases hcases with h | h | h
  · exact h
  · exact (big 103 (by norm_num) (by rw [h]; norm_num) (by norm_num)).elim
  · exact (big 167 (by norm_num) (by rw [h]; norm_num) (by norm_num)).elim

theorem prime_le_five_of_dvd_150 {p : ℕ} (hp : p.Prime) (h : p ∣ 150) : p ≤ 5 := by
  have h' : p ∣ 2 * (3 * (5 * 5)) := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · exact (Nat.le_of_dvd (by norm_num) h1).trans (by norm_num)
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3 <;>
    exact Nat.le_of_dvd (by norm_num) h3

theorem lyons_configuration_U_exact_numerical_solution (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℤ)
    (h₁ : 12 ≤ |x₁|) (h₂ : 12 ≤ |x₂|) (h₃ : 12 ≤ |x₃|) (h₄ : 12 ≤ |x₄|) (_h₅ : 12 ≤ |x₅|)
    (h₆ : 12 ≤ |x₆|) (h₇ : 12 ≤ |x₇|)
    (c₁ : x₁ ≡ 51 [ZMOD 64]) (c₂ : x₂ ≡ 52 [ZMOD 64]) (c₃ : x₃ ≡ 1 [ZMOD 64])
    (c₄ : x₄ ≡ 39 [ZMOD 64]) (c₅ : x₅ ≡ 42 [ZMOD 64]) (c₆ : x₆ ≡ 1 [ZMOD 64])
    (c₇ : x₇ ≡ 52 [ZMOD 64]) (h₅neg : x₅ < 0 → x₅ ≤ -150)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ x₁.natAbs ∨ p ∣ x₂.natAbs ∨ p ∣ x₃.natAbs ∨ p ∣ x₄.natAbs ∨
      p ∣ x₅.natAbs ∨ p ∣ x₆.natAbs ∨ p ∣ x₇.natAbs) →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1 ∧ (p : ℤ) ≤ |x₃| + 1 ∧ (p : ℤ) ≤ |x₄| + 1 ∧
        (p : ℤ) ≤ |x₇| + 1)
    (e₁ : (1 : ℚ) - 36 / x₁ + 4 / x₃ - 98 / x₄ + 200 / x₅ + 1 / x₆ = 0)
    (e₂ : (1 : ℚ) + 18 / x₁ + 16 / x₂ - 1 / x₃ - 49 / x₄ + 1 / x₆ - 16 / x₇ = 0)
    (e₃ : 0 < (1 : ℚ) + 36 / x₁ + 64 / x₂ + 98 / x₄ + 200 / x₅ + 1 / x₆) :
    x₁ = -13 ∧ x₂ = 52 ∧ x₃ = 65 ∧ x₄ = 39 ∧ x₅ = -150 ∧ x₆ = 65 ∧ x₇ = -12 := by
  have second := lyons_second_reciprocal_small_fourth_degree x₁ x₂ x₃ x₄ x₆ x₇ h₁ h₂ h₃ h₄ h₆ h₇
    c₁ c₂ c₇ c₃ c₆ c₄
  have hp4 : ∀ p : ℕ, p.Prime → p ∣ x₄.natAbs →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1 ∧ (p : ℤ) ≤ |x₃| + 1 ∧ (p : ℤ) ≤ |x₇| + 1 :=
    fun p hpp hd => by
      obtain ⟨q₁, q₂, q₃, -, q₇⟩ := hp p hpp (Or.inr (Or.inr (Or.inr (Or.inl hd))))
      exact ⟨q₁, q₂, q₃, q₇⟩
  have p53 : x₅ = 106 → (53 : ℤ) ≤ |x₂| + 1 ∧ (53 : ℤ) ≤ |x₄| + 1 := fun h => by
    obtain ⟨-, q₂, -, q₄, -⟩ := hp 53 (by norm_num)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; decide))))))
    exact ⟨q₂, q₄⟩
  simp only [Int.ModEq] at c₁ c₂ c₃ c₄ c₅ c₆ c₇
  have b₁ := inv_mem_of_le_or_le (A := 51) (B := 13) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁; omega)
  have b₃ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃ h₃; rw [le_abs'] at h₃; omega)
  have b₄ := inv_mem_of_le_or_le (A := 39) (B := 25) (by norm_num) (by norm_num) (x := x₄)
    (by clear * - c₄; omega)
  have b₅ := inv_mem_of_le_or_le (A := 42) (B := 150) (by norm_num) (by norm_num) (x := x₅)
    (by rcases lt_or_ge x₅ 0 with h | h
        · exact Or.inr (h₅neg h)
        · left; clear * - c₅ h; omega)
  have b₆ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₆)
    (by clear * - c₆ h₆; rw [le_abs'] at h₆; omega)
  push_cast at b₁ b₃ b₄ b₅ b₆
  simp only [div_eq_mul_inv] at e₁ e₂ e₃
  have n₅ : x₅ ≠ 42 := by
    intro h
    rw [h] at e₁
    push_cast at e₁
    linarith [b₁.2, b₄.2, b₃.1, b₆.1]
  have n₂ : x₂ ≠ -12 := by
    intro h
    have e₃' := e₃
    rw [h] at e₃'
    push_cast at e₃'
    have hlow : (3 / 400 : ℚ) < (x₅ : ℚ)⁻¹ := by linarith [b₃.2, b₆.2]
    obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hlt' : x₅ < 134 := by
      have : (x₅ : ℚ) < 134 := by norm_num at hlt; linarith
      exact_mod_cast this
    have h106 : x₅ = 106 := by clear * - hpos hlt' c₅ n₅; omega
    have := (p53 h106).1
    rw [h] at this
    norm_num at this
  have hx₁ : x₁ = -13 := by
    by_contra n₁
    have hx₄ : x₄ = 39 := second n₁ n₂ hp4 (by rw [← e₂]; simp only [div_eq_mul_inv])
    have b₁' := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₁)
      (by clear * - c₁ n₁; omega)
    push_cast at b₁'
    have e₁' := e₁
    rw [hx₄] at e₁'
    push_cast at e₁'
    have hlow : (3 / 650 : ℚ) < (x₅ : ℚ)⁻¹ := by linarith [b₁'.1, b₃.2, b₆.2]
    obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hlt' : x₅ < 217 := by
      have : (x₅ : ℚ) < 217 := by norm_num at hlt; linarith
      exact_mod_cast this
    have hc : x₅ = 106 ∨ x₅ = 170 := by clear * - hpos hlt' c₅ n₅; omega
    rcases hc with h | h
    · have := (p53 h).2
      rw [hx₄] at this
      norm_num at this
    · rw [h] at e₁'
      push_cast at e₁'
      have hup : (x₁ : ℚ)⁻¹ < -(1 / 139) := by linarith [b₃.2, b₆.2]
      obtain ⟨hneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
      have hgt' : -139 < x₁ := by
        have : (-139 : ℚ) < x₁ := by norm_num at hgt; linarith
        exact_mod_cast this
      have h77 : x₁ = -77 := by clear * - hneg hgt' c₁ n₁; omega
      rw [h77] at e₁'
      push_cast at e₁'
      linarith [b₃.1, b₆.1]
  rw [hx₁] at e₁ e₂ e₃
  push_cast at e₁ e₂ e₃
  have hx₄ : x₄ = 39 := by
    have hlow : (1 / 103 : ℚ) < (x₄ : ℚ)⁻¹ := by linarith [b₃.1, b₆.1, b₅.1]
    obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hlt' : x₄ < 103 := by
      have : (x₄ : ℚ) < 103 := by norm_num at hlt; linarith
      exact_mod_cast this
    clear * - hpos hlt' c₄
    omega
  rw [hx₄] at e₁ e₂ e₃
  push_cast at e₁ e₂ e₃
  have hx₅ : x₅ = -150 := by
    have hup : (x₅ : ℚ)⁻¹ < 0 := by linarith [b₃.1, b₆.1]
    have hneg : x₅ < 0 := by
      have : (x₅ : ℚ) < 0 := inv_lt_zero.mp hup
      exact_mod_cast this
    have h150 := h₅neg hneg
    by_contra hne
    have b₅' := inv_neg_ge_of_le (B := 214) (by norm_num) (x := x₅)
      (by clear * - h150 hne c₅; omega)
    push_cast at b₅'
    linarith [b₃.1, b₆.1, b₅'.1]
  rw [hx₅] at e₁ e₃
  push_cast at e₁ e₃
  have i₃ : (x₃ : ℚ)⁻¹ = 1 / 65 := by linarith [b₃.2, b₆.2]
  have i₆ : (x₆ : ℚ)⁻¹ = 1 / 65 := by linarith [b₃.2, b₆.2]
  have hx₃ : x₃ = 65 := by
    have : (x₃ : ℚ) = 65 := by rw [← inv_inv (x₃ : ℚ), i₃]; norm_num
    exact_mod_cast this
  have hx₆ : x₆ = 65 := by
    have : (x₆ : ℚ) = 65 := by rw [← inv_inv (x₆ : ℚ), i₆]; norm_num
    exact_mod_cast this
  rw [i₃, i₆] at e₂
  rw [i₆] at e₃
  have hx₂ : x₂ = 52 := by
    have hlow : (7 / 780 : ℚ) < (x₂ : ℚ)⁻¹ := by linarith
    obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hlt' : x₂ < 112 := by
      have : (x₂ : ℚ) < 112 := by norm_num at hlt; linarith
      exact_mod_cast this
    clear * - hpos hlt' c₂
    omega
  rw [hx₂] at e₂
  push_cast at e₂
  have i₇ : (x₇ : ℚ)⁻¹ = -(1 / 12) := by linarith
  have hx₇ : x₇ = -12 := by
    have : (x₇ : ℚ) = -12 := by rw [← inv_inv (x₇ : ℚ), i₇]; norm_num
    exact_mod_cast this
  exact ⟨hx₁, hx₂, hx₃, hx₄, hx₅, hx₆, hx₇⟩

theorem inv_mem_of_modEq_53 {t : ℤ} (hc : t ≡ 53 [ZMOD 64]) (hn : t < 0 → t ≤ -75) :
    -(1 / 75 : ℚ) ≤ (t : ℚ)⁻¹ ∧ (t : ℚ)⁻¹ ≤ 1 / 53 := by
  simp only [Int.ModEq] at hc
  have := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := t)
    (by rcases lt_or_ge t 0 with h | h
        · exact Or.inr (hn h)
        · left; omega)
  push_cast at this
  exact this

theorem inv_le_of_modEq_53_of_ne {t : ℤ} (hc : t ≡ 53 [ZMOD 64]) (hn : t < 0 → t ≤ -75)
    (hne : t ≠ 53) : (t : ℚ)⁻¹ ≤ 1 / 117 := by
  simp only [Int.ModEq] at hc
  have := inv_mem_of_le_or_le (A := 117) (B := 75) (by norm_num) (by norm_num) (x := t)
    (by rcases lt_or_ge t 0 with h | h
        · exact Or.inr (hn h)
        · left; omega)
  push_cast at this
  exact this.2

theorem inv_ge_of_modEq_53_of_ne {t : ℤ} (hc : t ≡ 53 [ZMOD 64]) (hn : t < 0 → t ≤ -75)
    (h75 : t ≠ -75) (h139 : t ≠ -139) : -(1 / 203 : ℚ) ≤ (t : ℚ)⁻¹ := by
  simp only [Int.ModEq] at hc
  have := inv_mem_of_le_or_le (A := 53) (B := 203) (by norm_num) (by norm_num) (x := t)
    (by rcases lt_or_ge t 0 with h | h
        · have := hn h
          right; omega
        · left; omega)
  push_cast at this
  exact this.1

theorem lyons_configuration_V_exact_numerical_solution (x₁ x₂ x₃ x₄ x₆ x₇ t₁ t₂ t₃ t₄ : ℤ)
    (h₁ : 12 ≤ |x₁|) (h₂ : 12 ≤ |x₂|) (h₃ : 12 ≤ |x₃|) (h₄ : 12 ≤ |x₄|) (h₆ : 12 ≤ |x₆|)
    (h₇ : 12 ≤ |x₇|) (_g₁ : 12 ≤ |t₁|) (_g₂ : 12 ≤ |t₂|) (_g₃ : 12 ≤ |t₃|) (_g₄ : 12 ≤ |t₄|)
    (c₁ : x₁ ≡ 51 [ZMOD 64]) (c₂ : x₂ ≡ 52 [ZMOD 64]) (c₇ : x₇ ≡ 52 [ZMOD 64])
    (c₃ : x₃ ≡ 1 [ZMOD 64]) (c₆ : x₆ ≡ 1 [ZMOD 64]) (c₄ : x₄ ≡ 39 [ZMOD 64])
    (d₁ : t₁ ≡ 53 [ZMOD 64]) (d₂ : t₂ ≡ 53 [ZMOD 64]) (d₃ : t₃ ≡ 53 [ZMOD 64])
    (d₄ : t₄ ≡ 53 [ZMOD 64])
    (n₁ : t₁ < 0 → t₁ ≤ -75) (n₂ : t₂ < 0 → t₂ ≤ -75) (n₃ : t₃ < 0 → t₃ ≤ -75)
    (n₄ : t₄ < 0 → t₄ ≤ -75)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ x₁.natAbs ∨ p ∣ x₂.natAbs ∨ p ∣ x₃.natAbs ∨ p ∣ x₄.natAbs ∨
      p ∣ x₆.natAbs ∨ p ∣ x₇.natAbs ∨ p ∣ t₁.natAbs ∨ p ∣ t₂.natAbs ∨ p ∣ t₃.natAbs ∨
        p ∣ t₄.natAbs) →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1 ∧ (p : ℤ) ≤ |x₃| + 1 ∧ (p : ℤ) ≤ |x₄| + 1 ∧
        (p : ℤ) ≤ |x₇| + 1)
    (e₁ : (1 : ℚ) - 36 / x₁ + 4 / x₃ - 98 / x₄ + (25 / t₁ + 25 / t₂ + 25 / t₃ + 25 / t₄) +
      1 / x₆ = 0)
    (e₂ : (1 : ℚ) + 18 / x₁ + 16 / x₂ - 1 / x₃ - 49 / x₄ + 1 / x₆ - 16 / x₇ = 0)
    (e₃ : 0 < (1 : ℚ) + 36 / x₁ + 64 / x₂ + 98 / x₄ + (25 / t₁ + 25 / t₂ + 25 / t₃ + 25 / t₄) +
      1 / x₆) :
    (x₁ = -13 ∧ x₂ = 52 ∧ x₃ = 65 ∧ x₄ = 39 ∧ x₆ = 65 ∧ x₇ = -12) ∧
      (t₁ = -75 ∧ t₂ = -75 ∧ t₃ = -75 ∧ t₄ = -75) := by
  have second := lyons_second_reciprocal_small_fourth_degree x₁ x₂ x₃ x₄ x₆ x₇ h₁ h₂ h₃ h₄ h₆ h₇
    c₁ c₂ c₇ c₃ c₆ c₄
  have hp4 : ∀ p : ℕ, p.Prime → p ∣ x₄.natAbs →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1 ∧ (p : ℤ) ≤ |x₃| + 1 ∧ (p : ℤ) ≤ |x₇| + 1 :=
    fun p hpp hd => by
      obtain ⟨q₁, q₂, q₃, -, q₇⟩ := hp p hpp (Or.inr (Or.inr (Or.inr (Or.inl hd))))
      exact ⟨q₁, q₂, q₃, q₇⟩
  have hU : t₁ = -75 → t₂ = -75 → t₃ = -75 → t₄ = -75 →
      x₁ = -13 ∧ x₂ = 52 ∧ x₃ = 65 ∧ x₄ = 39 ∧ (-150 : ℤ) = -150 ∧ x₆ = 65 ∧ x₇ = -12 := by
    rintro rfl rfl rfl rfl
    refine lyons_configuration_U_exact_numerical_solution x₁ x₂ x₃ x₄ (-150) x₆ x₇ h₁ h₂ h₃ h₄
      (by norm_num) h₆ h₇ c₁ c₂ c₃ c₄ (by decide) c₆ c₇ (fun _ => le_rfl) ?_ ?_ e₂ ?_
    · intro p hpp hd
      rcases hd with hd | hd | hd | hd | hd | hd | hd
      · exact hp p hpp (Or.inl hd)
      · exact hp p hpp (Or.inr (Or.inl hd))
      · exact hp p hpp (Or.inr (Or.inr (Or.inl hd)))
      · exact hp p hpp (Or.inr (Or.inr (Or.inr (Or.inl hd))))
      · have h5 : (p : ℤ) ≤ 5 := by
          exact_mod_cast prime_le_five_of_dvd_150 hpp (by simpa using hd)
        exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
      · exact hp p hpp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd)))))
      · exact hp p hpp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))))
    · push_cast at e₁ ⊢
      linarith
    · push_cast at e₃ ⊢
      linarith
  have no53 : ∀ B : ℤ, B < 52 → ((53 : ℤ) ≤ |x₁| + 1 ∧ (53 : ℤ) ≤ |x₂| + 1 ∧
      (53 : ℤ) ≤ |x₃| + 1 ∧ (53 : ℤ) ≤ |x₄| + 1 ∧ (53 : ℤ) ≤ |x₇| + 1 → (53 : ℤ) ≤ B + 1) →
      t₁ ≠ 53 ∧ t₂ ≠ 53 ∧ t₃ ≠ 53 ∧ t₄ ≠ 53 := by
    intro B hB hsel
    have hd : 53 ∣ (53 : ℤ).natAbs := by decide
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
      linarith [hsel (hp 53 (by norm_num) (by simp only [hd, or_true, true_or]))]
  have no139 : x₁ = -13 → t₁ ≠ -139 ∧ t₂ ≠ -139 ∧ t₃ ≠ -139 ∧ t₄ ≠ -139 := by
    intro hx
    have hd : 139 ∣ (-139 : ℤ).natAbs := by decide
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
    · have := (hp 139 (by norm_num) (by simp only [hd, or_true, true_or])).1
      rw [hx] at this
      norm_num at this
  simp only [Int.ModEq] at c₁ c₂ c₃ c₄ c₆ c₇
  have b₁ := inv_mem_of_le_or_le (A := 51) (B := 13) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁; omega)
  have b₃ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃ h₃; rw [le_abs'] at h₃; omega)
  have b₆ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₆)
    (by clear * - c₆ h₆; rw [le_abs'] at h₆; omega)
  push_cast at b₁ b₃ b₆
  have a₁ := inv_mem_of_modEq_53 d₁ n₁
  have a₂ := inv_mem_of_modEq_53 d₂ n₂
  have a₃ := inv_mem_of_modEq_53 d₃ n₃
  have a₄ := inv_mem_of_modEq_53 d₄ n₄
  simp only [div_eq_mul_inv] at e₁ e₂ e₃
  have nx₂ : x₂ ≠ -12 := by
    intro h
    obtain ⟨m₁, m₂, m₃, m₄⟩ := no53 |x₂| (by rw [h]; norm_num) fun q => q.2.1
    have := inv_le_of_modEq_53_of_ne d₁ n₁ m₁
    have := inv_le_of_modEq_53_of_ne d₂ n₂ m₂
    have := inv_le_of_modEq_53_of_ne d₃ n₃ m₃
    have := inv_le_of_modEq_53_of_ne d₄ n₄ m₄
    rw [h] at e₃
    push_cast at e₃
    linarith [b₃.2, b₆.2]
  have hx₁ : x₁ = -13 := by
    by_contra nx₁
    have hx₄ : x₄ = 39 := second nx₁ nx₂ hp4 (by rw [← e₂]; simp only [div_eq_mul_inv])
    have b₁' := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₁)
      (by clear * - c₁ nx₁; omega)
    push_cast at b₁'
    obtain ⟨m₁, m₂, m₃, m₄⟩ := no53 |x₄| (by rw [hx₄]; norm_num) fun q => q.2.2.2.1
    have := inv_le_of_modEq_53_of_ne d₁ n₁ m₁
    have := inv_le_of_modEq_53_of_ne d₂ n₂ m₂
    have := inv_le_of_modEq_53_of_ne d₃ n₃ m₃
    have := inv_le_of_modEq_53_of_ne d₄ n₄ m₄
    rw [hx₄] at e₁
    push_cast at e₁
    linarith [b₁'.1, b₃.2, b₆.2]
  obtain ⟨o₁, o₂, o₃, o₄⟩ := no139 hx₁
  rw [hx₁] at e₁ e₂ e₃
  push_cast at e₁ e₂ e₃
  have hx₄ : x₄ = 39 := by
    have hlow : (1 / 103 : ℚ) < (x₄ : ℚ)⁻¹ := by linarith [b₃.1, b₆.1, a₁.1, a₂.1, a₃.1, a₄.1]
    obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hlt' : x₄ < 103 := by
      have : (x₄ : ℚ) < 103 := by norm_num at hlt; linarith
      exact_mod_cast this
    clear * - hpos hlt' c₄
    omega
  rw [hx₄] at e₁ e₂ e₃
  push_cast at e₁ e₂ e₃
  have ht : t₁ = -75 ∧ t₂ = -75 ∧ t₃ = -75 ∧ t₄ = -75 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hne
    · linarith [inv_ge_of_modEq_53_of_ne d₁ n₁ hne o₁, a₂.1, a₃.1, a₄.1, b₃.1, b₆.1]
    · linarith [inv_ge_of_modEq_53_of_ne d₂ n₂ hne o₂, a₁.1, a₃.1, a₄.1, b₃.1, b₆.1]
    · linarith [inv_ge_of_modEq_53_of_ne d₃ n₃ hne o₃, a₁.1, a₂.1, a₄.1, b₃.1, b₆.1]
    · linarith [inv_ge_of_modEq_53_of_ne d₄ n₄ hne o₄, a₁.1, a₂.1, a₃.1, b₃.1, b₆.1]
  obtain ⟨r₁, r₂, r₃, r₄, -, r₆, r₇⟩ := hU ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
  exact ⟨⟨r₁, r₂, r₃, r₄, r₆, r₇⟩, ht⟩

end CFSG.LyonsUnitaryFour
