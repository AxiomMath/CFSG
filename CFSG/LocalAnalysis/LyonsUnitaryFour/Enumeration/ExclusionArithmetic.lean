module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Reciprocal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LyonsUnitaryFour

theorem lyons_four_cycle_le_neg_77 {x q : ℤ} (cx : x ≡ 51 [ZMOD 64]) (hq : 0 < q → 90 ≤ q)
    (hdeg : 8 * x + 4 * q = 0) (hpos : 0 < (72 : ℚ) / x + 400 / q) :
    q = -2 * x ∧ x ≤ -77 ∧ (q : ℚ)⁻¹ = -(1 / 2) * (x : ℚ)⁻¹ := by
  have hq2 : q = -2 * x := by omega
  have hqinv : (q : ℚ)⁻¹ = -(1 / 2) * (x : ℚ)⁻¹ := by
    rw [hq2]
    push_cast
    rw [mul_inv]
    norm_num
  simp only [div_eq_mul_inv, hqinv] at hpos
  have hxinv : (x : ℚ)⁻¹ < 0 := by linarith
  have hx : x < 0 := by
    have : (x : ℚ) < 0 := inv_lt_zero.mp hxinv
    exact_mod_cast this
  have h90 := hq (by omega)
  simp only [Int.ModEq] at cx
  exact ⟨hq2, by omega, hqinv⟩

theorem add_eq_mul_of_inv_add_inv {y₁ y₂ : ℤ} (h₁ : y₁ ≠ 0) (h₂ : y₂ ≠ 0) {r : ℚ}
    (h : (y₁ : ℚ)⁻¹ + (y₂ : ℚ)⁻¹ = r) : (y₁ : ℚ) + y₂ = r * y₁ * y₂ := by
  have h₁' : (y₁ : ℚ) ≠ 0 := by exact_mod_cast h₁
  have h₂' : (y₂ : ℚ) ≠ 0 := by exact_mod_cast h₂
  rw [← h]
  field_simp
  ring

theorem lyons_ADG_arithmetic (x q y₁ y₂ z₁ : ℤ) (hy₁ : 12 ≤ |y₁|) (hy₂ : 12 ≤ |y₂|)
    (cx : x ≡ 51 [ZMOD 64]) (cy₁ : y₁ ≡ 1 [ZMOD 64]) (cy₂ : y₂ ≡ 1 [ZMOD 64])
    (cz : z₁ ≡ 41 [ZMOD 64]) (hq : 0 < q → 90 ≤ q) (hdeg : 8 * x + 4 * q = 0)
    (hpos : 0 < (72 : ℚ) / x + 400 / q) (hL : 1 + 2 * x + y₁ + y₂ - z₁ = 0)
    (hE : (1 : ℚ) + 18 / x + 1 / y₁ + 1 / y₂ - 81 / z₁ = 0) : False := by
  obtain ⟨-, hx77, -⟩ := lyons_four_cycle_le_neg_77 cx hq hdeg hpos
  simp only [Int.ModEq] at cx cy₁ cy₂ cz
  have b₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₁)
    (by clear * - cy₁ hy₁; rw [le_abs'] at hy₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₂)
    (by clear * - cy₂ hy₂; rw [le_abs'] at hy₂; omega)
  have bx := inv_neg_ge_of_le (B := 77) (by norm_num) hx77
  push_cast at b₁ b₂ bx
  simp only [div_eq_mul_inv] at hE
  by_cases h77 : x = -77
  · subst h77
    push_cast at hE
    have hlow : (1 / 169 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1]
    have hup : (z₁ : ℚ)⁻¹ < 1 / 41 := by linarith [b₁.2, b₂.2]
    obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hzlt' : z₁ < 169 := by
      have : (z₁ : ℚ) < 169 := by norm_num at hzlt; exact hzlt
      exact_mod_cast this
    have hz41 : z₁ ≠ 41 := by
      rintro rfl
      norm_num at hup
    have hz : z₁ = 105 := by clear * - hzpos hzlt' cz hz41; omega
    subst hz
    push_cast at hE
    have hinv : (y₁ : ℚ)⁻¹ + (y₂ : ℚ)⁻¹ = 2 / 385 := by linarith
    have hsum : y₁ + y₂ = 258 := by linarith
    have hprod := add_eq_mul_of_inv_add_inv (by clear * - cy₁ hy₁; rw [le_abs'] at hy₁; omega)
      (by clear * - cy₂ hy₂; rw [le_abs'] at hy₂; omega) hinv
    have hprod' : y₁ * y₂ = 49665 := by
      have : ((y₁ * y₂ : ℤ) : ℚ) = 49665 := by
        push_cast
        have hs : ((y₁ + y₂ : ℤ) : ℚ) = 258 := by exact_mod_cast hsum
        push_cast at hs
        nlinarith
      exact_mod_cast this
    have hsq : (y₁ - y₂) ^ 2 = (y₁ + y₂) ^ 2 - 4 * (y₁ * y₂) := by ring
    rw [hsum, hprod'] at hsq
    nlinarith [sq_nonneg (y₁ - y₂)]
  · have bx' := inv_neg_ge_of_le (B := 141) (by norm_num) (x := x)
      (by clear * - hx77 h77 cx; omega)
    push_cast at bx'
    have hlow : (1 / 105 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1, bx'.1]
    have hup : (z₁ : ℚ)⁻¹ < 1 / 41 := by linarith [b₁.2, b₂.2, bx'.2]
    obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hzlt' : z₁ < 105 := by
      have : (z₁ : ℚ) < 105 := by norm_num at hzlt; exact hzlt
      exact_mod_cast this
    have hz : z₁ = 41 := by clear * - hzpos hzlt' cz; omega
    subst hz
    norm_num at hup

theorem lyons_CEF_arithmetic (x q y w₁ w₂ : ℤ) (hy : 12 ≤ |y|) (cx : x ≡ 51 [ZMOD 64])
    (cy : y ≡ 1 [ZMOD 64]) (cw₁ : w₁ ≡ 52 [ZMOD 64]) (cw₂ : w₂ ≡ 52 [ZMOD 64])
    (hq : 0 < q → 90 ≤ q) (hdeg : 8 * x + 4 * q = 0) (hpos : 0 < (72 : ℚ) / x + 400 / q)
    (hE : (1 : ℚ) + 18 / x + 1 / y - 16 / w₁ - 16 / w₂ = 0) : False := by
  obtain ⟨-, hx77, -⟩ := lyons_four_cycle_le_neg_77 cx hq hdeg hpos
  simp only [Int.ModEq] at cy cw₁ cw₂
  have bx := inv_neg_ge_of_le (B := 77) (by norm_num) hx77
  have by' := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy hy; rw [le_abs'] at hy; omega)
  have b₁ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₁)
    (by clear * - cw₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₂)
    (by clear * - cw₂; omega)
  push_cast at bx by' b₁ b₂
  simp only [div_eq_mul_inv] at hE
  linarith [bx.1, by'.1, b₁.2, b₂.2]

theorem lyons_H_arithmetic (x y z₁ : ℤ) (cx : x ≡ 53 [ZMOD 64]) (cy : y ≡ 51 [ZMOD 64])
    (cz : z₁ ≡ 37 [ZMOD 64]) (nx : x < 0 → x ≤ -75) (pz : 0 < z₁ → 165 ≤ z₁)
    (hL : 1 + 4 * x - 2 * y - 3 * z₁ = 0)
    (hE : (1 : ℚ) + 100 / x - 18 / y - 75 / z₁ = 0) : False := by
  simp only [Int.ModEq] at cx cy cz
  have hy0 : y ≠ 0 := by clear * - cy; omega
  have hz0 : z₁ ≠ 0 := by clear * - cz; omega
  have by' := inv_mem_of_le_or_le (A := 51) (B := 13) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy; omega)
  have bz := inv_mem_of_le_or_le (A := 165) (B := 27) (by norm_num) (by norm_num) (x := z₁)
    (by rcases lt_or_ge 0 z₁ with h | h
        · exact Or.inl (pz h)
        · right; clear * - cz h; omega)
  push_cast at by' bz
  simp only [div_eq_mul_inv] at hE
  have hxneg : x < 0 := by
    by_contra hx
    have bx := inv_pos_le_of_le (A := 53) (by norm_num) (x := x) (by clear * - cx hx; omega)
    linarith [bx.1, by'.2, bz.2]
  have hx75 := nx hxneg
  have hsmall : 18 * (y : ℚ)⁻¹ + 75 * (z₁ : ℚ)⁻¹ < 5 / 11 := by
    rcases lt_or_ge y 0 with hyn | hyn
    · have : (y : ℚ)⁻¹ < 0 := inv_lt_zero.mpr (by exact_mod_cast hyn)
      linarith [bz.2]
    · have hzn : z₁ < 0 := by omega
      have : (z₁ : ℚ)⁻¹ < 0 := inv_lt_zero.mpr (by exact_mod_cast hzn)
      linarith [by'.2]
  have hxup : (x : ℚ)⁻¹ < -(3 / 550) := by linarith
  obtain ⟨-, hxgt⟩ := neg_gt_of_inv_lt (by norm_num) hxup
  have hxgt' : -184 < x := by
    have : (-184 : ℚ) < x := by norm_num at hxgt; linarith
    exact_mod_cast this
  have hcases : x = -75 ∨ x = -139 := by clear * - hx75 hxgt' cx; omega
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy0
  have hz' : (z₁ : ℚ) ≠ 0 := by exact_mod_cast hz0
  have hL' : (1 : ℚ) + 4 * x - 2 * y - 3 * z₁ = 0 := by exact_mod_cast hL
  rcases hcases with rfl | rfl
  · push_cast at hE hL'
    have hmul : (-(1 : ℚ) / 3) * (y * z₁) - 18 * z₁ - 75 * y = 0 := by
      have h1 : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy'
      have h2 : (z₁ : ℚ) * (z₁ : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hz'
      linear_combination (↑y * ↑z₁) * hE + 18 * ↑z₁ * h1 + 75 * ↑y * h2
    have key : 3 * (z₁ : ℚ) ^ 2 + 866 * z₁ + 67275 = 0 := by
      linear_combination 6 * hmul + (-(↑z₁ : ℚ) - 225) * hL'
    nlinarith [sq_nonneg (3 * (z₁ : ℚ) + 433)]
  · push_cast at hE hL'
    have hmul : (39 / 139 : ℚ) * (y * z₁) - 18 * z₁ - 75 * y = 0 := by
      have h1 : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy'
      have h2 : (z₁ : ℚ) * (z₁ : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hz'
      linear_combination (↑y * ↑z₁) * hE + 18 * ↑z₁ * h1 + 75 * ↑y * h2
    have key : 13 * (z₁ : ℚ) ^ 2 - 514 * z₁ - 642875 = 0 := by
      linear_combination (-(278 / 9 : ℚ)) * hmul + ((-(13 : ℚ) / 3) * ↑z₁ + 3475 / 3) * hL'
    have keyZ : 13 * z₁ ^ 2 - 514 * z₁ - 642875 = 0 := by exact_mod_cast key
    have hsq : (26 * z₁ - 514) ^ 2 = 33693696 := by linear_combination 52 * keyZ
    rcases le_or_gt (26 * z₁ - 514) 5804 with h1 | h1
    · rcases le_or_gt (-5804) (26 * z₁ - 514) with h2 | h2
      · have := sq_le_sq' h2 h1
        linarith
      · have hw : (5805 : ℤ) ≤ -(26 * z₁ - 514) := by omega
        have := pow_le_pow_left₀ (by norm_num) hw 2
        rw [neg_sq] at this
        linarith
    · have hw : (5805 : ℤ) ≤ 26 * z₁ - 514 := by omega
      have := pow_le_pow_left₀ (by norm_num) hw 2
      linarith

theorem lyons_M_arithmetic (x₁ x₂ x₃ q y₁ y₂ w : ℤ) (h₁ : 12 ≤ |x₁|) (h₂ : 12 ≤ |x₂|)
    (h₃ : 12 ≤ |x₃|) (_hq : 12 ≤ |q|) (g₁ : 12 ≤ |y₁|) (g₂ : 12 ≤ |y₂|) (_hw : 12 ≤ |w|)
    (c₁ : x₁ ≡ 1 [ZMOD 64]) (c₂ : x₂ ≡ 1 [ZMOD 64]) (c₃ : x₃ ≡ 1 [ZMOD 64])
    (d₁ : y₁ ≡ 1 [ZMOD 64]) (d₂ : y₂ ≡ 1 [ZMOD 64]) (cq : q ≡ 52 [ZMOD 64])
    (cw : w ≡ 52 [ZMOD 64])
    (hE : (1 : ℚ) - 1 / x₁ - 1 / x₂ - 1 / x₃ + 16 / q + 1 / y₁ + 1 / y₂ - 16 / w = 0) :
    False := by
  simp only [Int.ModEq] at c₁ c₂ c₃ d₁ d₂ cq cw
  have b₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ h₁; rw [le_abs'] at h₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ h₂; rw [le_abs'] at h₂; omega)
  have b₃ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₃)
    (by clear * - c₃ h₃; rw [le_abs'] at h₃; omega)
  have a₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₁)
    (by clear * - d₁ g₁; rw [le_abs'] at g₁; omega)
  have a₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₂)
    (by clear * - d₂ g₂; rw [le_abs'] at g₂; omega)
  have bw := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w)
    (by clear * - cw; omega)
  push_cast at b₁ b₂ b₃ a₁ a₂ bw
  simp only [div_eq_mul_inv] at hE
  by_cases hq12 : q = -12
  · subst hq12
    push_cast at hE
    have hwneg : (w : ℚ)⁻¹ < 0 := by linarith [b₁.1, b₂.1, b₃.1, a₁.2, a₂.2]
    have hw : w < 0 := by
      have : (w : ℚ) < 0 := inv_lt_zero.mp hwneg
      exact_mod_cast this
    by_cases hw12 : w = -12
    · subst hw12
      push_cast at hE
      linarith [b₁.2, b₂.2, b₃.2, a₁.1, a₂.1]
    · have bw' := inv_neg_ge_of_le (B := 76) (by norm_num) (x := w)
        (by clear * - hw hw12 cw; omega)
      push_cast at bw'
      linarith [b₁.1, b₂.1, b₃.1, a₁.2, a₂.2, bw'.1]
  · have bq := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := q)
      (by clear * - cq hq12; omega)
    push_cast at bq
    linarith [b₁.2, b₂.2, b₃.2, a₁.1, a₂.1, bq.1, bw.2]

theorem lyons_Q_arithmetic (x h₁ h₂ h₃ z₁ y w : ℤ) (hx : 12 ≤ |x|) (hy : 12 ≤ |y|)
    (cx : x ≡ 1 [ZMOD 64]) (cy : y ≡ 1 [ZMOD 64]) (c₁ : h₁ ≡ 52 [ZMOD 64])
    (c₂ : h₂ ≡ 52 [ZMOD 64]) (c₃ : h₃ ≡ 52 [ZMOD 64]) (cw : w ≡ 52 [ZMOD 64])
    (cz : z₁ ≡ 37 [ZMOD 64]) (pz : 0 < z₁ → 165 ≤ z₁)
    (hE : (2 : ℚ) + 3 / x + 16 / h₁ + 16 / h₂ + 16 / h₃ - 75 / z₁ + 2 / y - 16 / w = 0)
    (hP : 0 < -(4 : ℚ) / x + 64 / h₁ + 64 / h₂ + 64 / h₃ + 100 / z₁) : False := by
  simp only [Int.ModEq] at cx cy c₁ c₂ c₃ cw cz
  have bx := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x)
    (by clear * - cx hx; rw [le_abs'] at hx; omega)
  have by' := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy hy; rw [le_abs'] at hy; omega)
  have b₁ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := h₁)
    (by clear * - c₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := h₂)
    (by clear * - c₂; omega)
  have b₃ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := h₃)
    (by clear * - c₃; omega)
  have bw := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w)
    (by clear * - cw; omega)
  have bz := inv_mem_of_le_or_le (A := 165) (B := 27) (by norm_num) (by norm_num) (x := z₁)
    (by rcases lt_or_ge 0 z₁ with h | h
        · exact Or.inl (pz h)
        · right; clear * - cz h; omega)
  push_cast at bx by' b₁ b₂ b₃ bw bz
  simp only [div_eq_mul_inv] at hE hP
  have far : ∀ h : ℤ, h % 64 = 52 % 64 → (h = h₁ ∨ h = h₂ ∨ h = h₃) →
      -(1 / 76 : ℚ) ≤ (h : ℚ)⁻¹ := by
    intro h ch hmem
    by_cases h12 : h = -12
    · subst h12
      exfalso
      rcases hmem with rfl | rfl | rfl <;> push_cast at hP <;>
        linarith [bx.1, b₁.2, b₂.2, b₃.2, bz.2]
    · have := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := h)
        (by clear * - ch h12; omega)
      push_cast at this
      exact this.1
  have f₁ := far h₁ c₁ (Or.inl rfl)
  have f₂ := far h₂ c₂ (Or.inr (Or.inl rfl))
  have f₃ := far h₃ c₃ (Or.inr (Or.inr rfl))
  have hlow : (1 / 165 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [bx.1, by'.1, bw.2]
  obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hzlt' : z₁ < 165 := by
    have : (z₁ : ℚ) < 165 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have := pz hzpos
  omega

theorem lyons_R_arithmetic (x z₁ h₁ h₂ : ℤ) (hx : 12 ≤ |x|) (cx : x ≡ 1 [ZMOD 64])
    (cz : z₁ ≡ 37 [ZMOD 64]) (c₁ : h₁ ≡ 53 [ZMOD 64]) (c₂ : h₂ ≡ 53 [ZMOD 64])
    (pz : 0 < z₁ → 165 ≤ z₁) (n₁ : h₁ < 0 → h₁ ≤ -75) (n₂ : h₂ < 0 → h₂ ≤ -75)
    (hL : 1 + 4 * x - 3 * z₁ + h₁ + h₂ = 0)
    (hE : (1 : ℚ) + 4 / x - 75 / z₁ + 25 / h₁ + 25 / h₂ = 0) : False := by
  simp only [Int.ModEq] at cx cz c₁ c₂
  have bx := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x)
    (by clear * - cx hx; rw [le_abs'] at hx; omega)
  have b₁ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := h₁)
    (by rcases lt_or_ge h₁ 0 with h | h
        · exact Or.inr (n₁ h)
        · left; clear * - c₁ h; omega)
  have b₂ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := h₂)
    (by rcases lt_or_ge h₂ 0 with h | h
        · exact Or.inr (n₂ h)
        · left; clear * - c₂ h; omega)
  push_cast at bx b₁ b₂
  simp only [div_eq_mul_inv] at hE
  have hzinv : (0 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [bx.1, b₁.1, b₂.1]
  have hzpos : 0 < z₁ := by
    have : (0 : ℚ) < z₁ := inv_pos.mp hzinv
    exact_mod_cast this
  have hz165 := pz hzpos
  have hD : (1 / 225 : ℚ) < (z₁ : ℚ)⁻¹ := by
    rcases lt_or_ge 0 x with hxp | hxp
    · have : (0 : ℚ) < (x : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hxp)
      linarith [b₁.1, b₂.1]
    · rcases lt_or_ge 0 h₁ with hp₁ | hp₁
      · have : (0 : ℚ) < (h₁ : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp₁)
        linarith [bx.1, b₂.1]
      · rcases lt_or_ge 0 h₂ with hp₂ | hp₂
        · have : (0 : ℚ) < (h₂ : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp₂)
          linarith [bx.1, b₁.1]
        · exfalso
          have : x ≤ -63 := by clear * - hxp cx hx; rw [le_abs'] at hx; omega
          omega
  obtain ⟨-, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hD
  have hzlt' : z₁ < 225 := by
    have : (z₁ : ℚ) < 225 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have hz : z₁ = 165 := by clear * - hz165 hzlt' cz; omega
  subst hz
  push_cast at hE
  have far : ∀ h : ℤ, h % 64 = 53 % 64 → (h < 0 → h ≤ -75) → h ≠ -75 →
      -(1 / 139 : ℚ) ≤ (h : ℚ)⁻¹ := by
    intro h ch nh h75
    have := inv_mem_of_le_or_le (A := 53) (B := 139) (by norm_num) (by norm_num) (x := h)
      (by rcases lt_or_ge h 0 with h' | h'
          · have := nh h'
            right; clear * - ch this h75; omega
          · left; clear * - ch h'; omega)
    push_cast at this
    exact this.1
  have finish : ∀ h h' : ℤ, h' % 64 = 53 % 64 → (h' < 0 → h' ≤ -75) → h = -75 →
      1 + 4 * x - 3 * 165 + h + h' = 0 →
      (1 : ℚ) + 4 * (x : ℚ)⁻¹ - 75 * 165⁻¹ + 25 * (h : ℚ)⁻¹ + 25 * (h' : ℚ)⁻¹ = 0 → False := by
    intro h h' ch' nh' hh hL' hE'
    subst hh
    push_cast at hE'
    have bh' : (h' : ℚ)⁻¹ < 0 := by linarith [bx.1, bx.2]
    have hneg : h' < 0 := by
      have : (h' : ℚ) < 0 := inv_lt_zero.mp bh'
      exact_mod_cast this
    have hxp : 0 < x := by omega
    have : (0 : ℚ) < (x : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hxp)
    have hup : (h' : ℚ)⁻¹ < -(7 / 825) := by linarith
    obtain ⟨-, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hgt' : -118 < h' := by
      have : (-118 : ℚ) < h' := by norm_num at hgt; linarith
      exact_mod_cast this
    have := nh' hneg
    clear * - hgt' this ch' hL' cx
    omega
  by_cases m₁ : h₁ = -75
  · exact finish h₁ h₂ c₂ n₂ m₁ (by linarith) (by linarith)
  · by_cases m₂ : h₂ = -75
    · exact finish h₂ h₁ c₁ n₁ m₂ (by linarith) (by linarith)
    · linarith [far h₁ c₁ n₁ m₁, far h₂ c₂ n₂ m₂, bx.1]

theorem lyons_S_arithmetic (x q h₁ h₂ w : ℤ) (cx : x ≡ 51 [ZMOD 64]) (cq : q ≡ 50 [ZMOD 64])
    (c₁ : h₁ ≡ 53 [ZMOD 64]) (c₂ : h₂ ≡ 53 [ZMOD 64]) (cw : w ≡ 52 [ZMOD 64])
    (pq : 0 < q → 114 ≤ q) (n₁ : h₁ < 0 → h₁ ≤ -75) (n₂ : h₂ < 0 → h₂ ≤ -75)
    (hE : (8 : ℚ) - 144 / x - 96 / q + 100 / h₁ + 100 / h₂ - 64 / w < 0) : False := by
  simp only [Int.ModEq] at cx cq c₁ c₂ cw
  have bx := inv_mem_of_le_or_le (A := 51) (B := 13) (by norm_num) (by norm_num) (x := x)
    (by clear * - cx; omega)
  have bq := inv_mem_of_le_or_le (A := 114) (B := 14) (by norm_num) (by norm_num) (x := q)
    (by rcases lt_or_ge 0 q with h | h
        · exact Or.inl (pq h)
        · right; clear * - cq h; omega)
  have b₁ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := h₁)
    (by rcases lt_or_ge h₁ 0 with h | h
        · exact Or.inr (n₁ h)
        · left; clear * - c₁ h; omega)
  have b₂ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := h₂)
    (by rcases lt_or_ge h₂ 0 with h | h
        · exact Or.inr (n₂ h)
        · left; clear * - c₂ h; omega)
  have bw := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w)
    (by clear * - cw; omega)
  push_cast at bx bq b₁ b₂ bw
  simp only [div_eq_mul_inv] at hE
  linarith [bx.2, bq.2, b₁.1, b₂.1, bw.2]

end CFSG.LyonsUnitaryFour
