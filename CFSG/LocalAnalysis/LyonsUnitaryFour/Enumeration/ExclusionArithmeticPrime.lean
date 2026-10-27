module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmetic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LyonsUnitaryFour

private theorem lyons_B_neg77 (a₁ a₂ z₁ h w : ℤ) (ca₁ : a₁ % 64 = 53 % 64)
    (ca₂ : a₂ % 64 = 53 % 64) (cz : z₁ % 64 = 41 % 64) (cw : w % 64 = 52 % 64)
    (na₁ : a₁ < 0 → a₁ ≤ -75) (na₂ : a₂ < 0 → a₂ ≤ -75) (nh : h < 0 → h ≤ -138)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ z₁.natAbs ∨ p ∣ h.natAbs) → (p : ℤ) ≤ |w| + 1)
    (ba₁ : -(1 / 75 : ℚ) ≤ (a₁ : ℚ)⁻¹) (ba₂ : -(1 / 75 : ℚ) ≤ (a₂ : ℚ)⁻¹)
    (bh : -(1 / 138 : ℚ) ≤ (h : ℚ)⁻¹) (bw : (w : ℚ)⁻¹ ≤ 1 / 52)
    (hE₁ : 1 + 18 * (-77 : ℚ)⁻¹ - 81 * (z₁ : ℚ)⁻¹ + 36 * (h : ℚ)⁻¹ - 16 * (w : ℚ)⁻¹ = 0)
    (hE₂ : 2 + 82 * (-77 : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 108 * (h : ℚ)⁻¹ -
      16 * (w : ℚ)⁻¹ = 0)
    (hD : 1 + 64 * (-77 : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 72 * (h : ℚ)⁻¹ +
      81 * (z₁ : ℚ)⁻¹ = 0)
    (hL₁ : 1 + 2 * (-77) - z₁ + h - w = 0) (hL₂ : 1 + a₁ + a₂ + z₁ + 2 * h = 0) : False := by
  have pos_inv : ∀ y : ℤ, 0 < y → (0 : ℚ) < (y : ℚ)⁻¹ := fun y hy =>
    inv_pos.mpr (by exact_mod_cast hy)
  have neg_inv : ∀ y : ℤ, y < 0 → (y : ℚ)⁻¹ < 0 := fun y hy =>
    inv_lt_zero.mpr (by exact_mod_cast hy)
  have a₁0 : a₁ ≠ 0 := by clear * - ca₁; omega
  have a₂0 : a₂ ≠ 0 := by clear * - ca₂; omega
  have far_a : ∀ a : ℤ, a % 64 = 53 % 64 → (a < 0 → a ≤ -75) → a ≠ -75 → a < 0 →
      -(1 / (139 : ℚ)) ≤ (a : ℚ)⁻¹ := by
    intro a ca na hne hneg
    have := inv_neg_ge_of_le (B := 139) (by norm_num) (x := a)
      (by have := na hneg; clear * - ca this hne; omega)
    push_cast at this
    exact this.1
  have hhneg : h < 0 := by
    by_contra hhpos
    have hhpos' : 0 < h := by
      have : h ≠ 0 := by
        rintro rfl
        clear * - hL₁ hL₂ cz cw
        omega
      omega
    have hpos := pos_inv h hhpos'
    have m₁ : a₁ = -75 := by
      by_contra hne
      rcases lt_or_gt_of_ne a₁0 with h₁ | h₁
      · linarith [far_a a₁ ca₁ na₁ hne h₁]
      · linarith [pos_inv a₁ h₁]
    have m₂ : a₂ = -75 := by
      by_contra hne
      rcases lt_or_gt_of_ne a₂0 with h₂ | h₂
      · linarith [far_a a₂ ca₂ na₂ hne h₂]
      · linarith [pos_inv a₂ h₂]
    subst m₁ m₂
    push_cast at hE₂
    have hw52 : w = 52 := by
      by_contra hne
      rcases lt_or_gt_of_ne (show w ≠ 0 by clear * - cw; omega) with hw | hw
      · linarith [neg_inv w hw]
      · have := inv_pos_le_of_le (A := 116) (by norm_num) (x := w)
          (by clear * - cw hw hne; omega)
        push_cast at this
        linarith [this.2]
    subst hw52
    have h118 : h = 118 := by clear * - hL₁ hL₂; omega
    have := hp 59 (by norm_num) (Or.inr (by rw [h118]; decide))
    norm_num at this
  have hh138 := nh hhneg
  have hzpos : 0 < z₁ := by
    by_contra hzn
    have hzn' : z₁ < 0 := by clear * - hzn cz; omega
    linarith [neg_inv z₁ hzn']
  have hwneg : w < 0 := by clear * - hzpos hL₁ hhneg; omega
  have hwinv := neg_inv w hwneg
  have hlow : (1 / 169 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith
  obtain ⟨-, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hzlt' : z₁ < 169 := by
    have : (z₁ : ℚ) < 169 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have hz : z₁ = 41 ∨ z₁ = 105 := by clear * - hzpos hzlt' cz; omega
  rcases hz with hz | hz
  · subst hz
    push_cast at hE₁
    have hup : (w : ℚ)⁻¹ < -(1 / 76) := by linarith [neg_inv h hhneg]
    obtain ⟨-, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hgt' : -76 < w := by
      have : (-76 : ℚ) < w := by norm_num at hgt; linarith
      exact_mod_cast this
    have hw12 : w = -12 := by clear * - hgt' hwneg cw; omega
    have := hp 41 (by norm_num) (Or.inl (by decide))
    rw [hw12] at this
    norm_num at this
  · subst hz
    push_cast at hD
    have hsum : 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ < -(1 / 3) := by linarith
    have hpos' : 0 < a₁ ∨ 0 < a₂ := by
      by_contra hc
      simp only [not_or, not_lt] at hc
      clear * - hc hL₂ hh138
      omega
    rcases hpos' with h₁ | h₂
    · have hup : (a₂ : ℚ)⁻¹ < -(1 / 75) := by linarith [pos_inv a₁ h₁]
      obtain ⟨hneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
      have hgt' : -75 < a₂ := by
        have : (-75 : ℚ) < a₂ := by norm_num at hgt; linarith
        exact_mod_cast this
      have := na₂ hneg
      omega
    · have hup : (a₁ : ℚ)⁻¹ < -(1 / 75) := by linarith [pos_inv a₂ h₂]
      obtain ⟨hneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
      have hgt' : -75 < a₁ := by
        have : (-75 : ℚ) < a₁ := by norm_num at hgt; linarith
        exact_mod_cast this
      have := na₁ hneg
      omega

private theorem lyons_B_uniform (x a₁ a₂ h w : ℤ) (cx ch ca : ℚ) (hca : 0 ≤ ca) (a₁0 : a₁ ≠ 0)
    (a₂0 : a₂ ≠ 0) (w0 : w ≠ 0) (hsign : 0 < w → 0 < a₁ ∨ 0 < a₂ ∨ 0 < h) (bw : (w : ℚ)⁻¹ ≤ 1 / 52)
    (hE₂ : 2 + 82 * (x : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 108 * (h : ℚ)⁻¹ -
      16 * (w : ℚ)⁻¹ = 0)
    (hx : -cx ≤ (x : ℚ)⁻¹) (hh : -ch ≤ (h : ℚ)⁻¹) (hhneg : h < 0)
    (hm₁ : a₁ < 0 → -ca ≤ (a₁ : ℚ)⁻¹) (hm₂ : a₂ < 0 → -ca ≤ (a₂ : ℚ)⁻¹)
    (hb₁ : 82 * cx + 25 * ca + 108 * ch + 16 / 52 < 2) (hb₂ : 82 * cx + 50 * ca + 108 * ch < 2) :
    False := by
  have pos_inv : ∀ y : ℤ, 0 < y → (0 : ℚ) < (y : ℚ)⁻¹ := fun y hy =>
    inv_pos.mpr (by exact_mod_cast hy)
  have neg_inv : ∀ y : ℤ, y < 0 → (y : ℚ)⁻¹ < 0 := fun y hy =>
    inv_lt_zero.mpr (by exact_mod_cast hy)
  rcases lt_or_gt_of_ne w0 with hw | hw
  · have := neg_inv w hw
    rcases lt_or_gt_of_ne a₁0 with h₁ | h₁ <;> rcases lt_or_gt_of_ne a₂0 with h₂ | h₂
    · linarith [hm₁ h₁, hm₂ h₂]
    · linarith [hm₁ h₁, pos_inv a₂ h₂]
    · linarith [pos_inv a₁ h₁, hm₂ h₂]
    · linarith [pos_inv a₁ h₁, pos_inv a₂ h₂]
  · rcases hsign hw with h₁ | h₂ | h'
    · rcases lt_or_gt_of_ne a₂0 with h₂ | h₂
      · linarith [pos_inv a₁ h₁, hm₂ h₂]
      · linarith [pos_inv a₁ h₁, pos_inv a₂ h₂]
    · rcases lt_or_gt_of_ne a₁0 with h₁ | h₁
      · linarith [hm₁ h₁, pos_inv a₂ h₂]
      · linarith [pos_inv a₁ h₁, pos_inv a₂ h₂]
    · omega

private theorem lyons_B_le141 (x a₁ a₂ z₁ h w : ℤ) (cx : x % 64 = 51 % 64)
    (ca₁ : a₁ % 64 = 53 % 64) (ca₂ : a₂ % 64 = 53 % 64) (ch : h % 64 = 54 % 64)
    (cw : w % 64 = 52 % 64) (na₁ : a₁ < 0 → a₁ ≤ -75) (na₂ : a₂ < 0 → a₂ ≤ -75)
    (nh : h < 0 → h ≤ -138) (hx141 : x ≤ -141)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ z₁.natAbs ∨ p ∣ h.natAbs) → (p : ℤ) ≤ |x| + 1)
    (ba₁ : -(1 / 75 : ℚ) ≤ (a₁ : ℚ)⁻¹) (ba₂ : -(1 / 75 : ℚ) ≤ (a₂ : ℚ)⁻¹)
    (bh : -(1 / 138 : ℚ) ≤ (h : ℚ)⁻¹) (bw : (w : ℚ)⁻¹ ≤ 1 / 52)
    (hsign : 0 < w → 0 < a₁ ∨ 0 < a₂ ∨ 0 < h)
    (hE₂ : 2 + 82 * (x : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 108 * (h : ℚ)⁻¹ -
      16 * (w : ℚ)⁻¹ = 0)
    (hD : 1 + 64 * (x : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 72 * (h : ℚ)⁻¹ +
      81 * (z₁ : ℚ)⁻¹ = 0)
    (hL₁ : 1 + 2 * x - z₁ + h - w = 0) (hL₂ : 1 + a₁ + a₂ + z₁ + 2 * h = 0) : False := by
  have pos_inv : ∀ y : ℤ, 0 < y → (0 : ℚ) < (y : ℚ)⁻¹ := fun y hy =>
    inv_pos.mpr (by exact_mod_cast hy)
  have neg_inv : ∀ y : ℤ, y < 0 → (y : ℚ)⁻¹ < 0 := fun y hy =>
    inv_lt_zero.mpr (by exact_mod_cast hy)
  have a₁0 : a₁ ≠ 0 := by clear * - ca₁; omega
  have a₂0 : a₂ ≠ 0 := by clear * - ca₂; omega
  have w0 : w ≠ 0 := by clear * - cw; omega
  have bx := inv_neg_ge_of_le (B := 141) (by norm_num) hx141
  push_cast at bx
  have hhneg : h < 0 := by
    by_contra hhpos
    have hhpos' : 0 < h := by
      have : h ≠ 0 := by clear * - ch; omega
      omega
    linarith [pos_inv h hhpos', bx.1]
  have hh138 := nh hhneg
  have hh : h = -138 := by
    by_contra hne
    have bh' := inv_neg_ge_of_le (B := 202) (by norm_num) (x := h)
      (by clear * - hh138 hne ch; omega)
    push_cast at bh'
    exact lyons_B_uniform x a₁ a₂ h w (1 / 141) (1 / 202) (1 / 75) (by norm_num) a₁0 a₂0 w0
      hsign bw hE₂ bx.1 bh'.1 hhneg (fun _ => ba₁) (fun _ => ba₂) (by norm_num) (by norm_num)
  subst hh
  have hx' : x = -141 := by
    by_contra hne
    have bx' := inv_neg_ge_of_le (B := 205) (by norm_num) (x := x)
      (by clear * - hx141 hne cx; omega)
    push_cast at bx'
    exact lyons_B_uniform x a₁ a₂ (-138) w (1 / 205) (1 / 138) (1 / 75) (by norm_num) a₁0 a₂0
      w0 hsign bw hE₂
      bx'.1 bh hhneg (fun _ => ba₁) (fun _ => ba₂) (by norm_num) (by norm_num)
  subst hx'
  push_cast at hE₂ hD
  have far_a : ∀ a : ℤ, a % 64 = 53 % 64 → (a < 0 → a ≤ -75) → a ≠ -75 → a < 0 →
      -(1 / (139 : ℚ)) ≤ (a : ℚ)⁻¹ := by
    intro a ca na hne hneg
    have := inv_neg_ge_of_le (B := 139) (by norm_num) (x := a)
      (by have := na hneg; clear * - ca this hne; omega)
    push_cast at this
    exact this.1
  have key : ∀ a a' : ℤ, a = -75 → a' % 64 = 53 % 64 → (a' < 0 → a' ≤ -75) →
      (2 + 82 * (-141 : ℚ)⁻¹ + 25 * (a : ℚ)⁻¹ + 25 * (a' : ℚ)⁻¹ +
        108 * (-138 : ℚ)⁻¹ - 16 * (w : ℚ)⁻¹ = 0) →
      (1 + 64 * (-141 : ℚ)⁻¹ + 25 * (a : ℚ)⁻¹ + 25 * (a' : ℚ)⁻¹ +
        72 * (-138 : ℚ)⁻¹ + 81 * (z₁ : ℚ)⁻¹ = 0) →
      (1 + a + a' + z₁ + 2 * (-138) = 0) → False := by
    intro a a' ha ca' na' hE' hD' hL'
    subst ha
    push_cast at hE' hD'
    rcases lt_or_ge a' 0 with ha' | ha'
    ·
      have hz : 425 ≤ z₁ := by have := na' ha'; omega
      have := inv_pos_le_of_le (A := 425) (by norm_num) hz
      push_cast at this
      linarith [neg_inv a' ha', this.2]
    · have ha'pos : 0 < a' := by clear * - ha' ca'; omega
      have hlow : (1 / 116 : ℚ) < (w : ℚ)⁻¹ := by linarith [pos_inv a' ha'pos]
      obtain ⟨hwpos, hwlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
      have hwlt' : w < 116 := by
        have : (w : ℚ) < 116 := by norm_num at hwlt; exact hwlt
        exact_mod_cast this
      have hw52 : w = 52 := by clear * - hwpos hwlt' cw; omega
      have hz : z₁ = -471 := by clear * - hL₁ hw52; omega
      have := hp 157 (by norm_num) (Or.inl (by rw [hz]; decide))
      norm_num at this
  by_cases m₁ : a₁ = -75
  · exact key a₁ a₂ m₁ ca₂ na₂ hE₂ hD hL₂
  · by_cases m₂ : a₂ = -75
    · exact key a₂ a₁ m₂ ca₁ na₁ (by linarith) (by linarith) (by linarith)
    · exact lyons_B_uniform (-141) a₁ a₂ (-138) w (1 / 141) (1 / 138) (1 / 139) (by norm_num)
        a₁0 a₂0 w0
        hsign bw (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
        hhneg (fun h₁ => far_a a₁ ca₁ na₁ m₁ h₁) (fun h₂ => far_a a₂ ca₂ na₂ m₂ h₂)
        (by norm_num) (by norm_num)

theorem lyons_B_arithmetic (x q a₁ a₂ z₁ h w : ℤ) (cx : x ≡ 51 [ZMOD 64])
    (ca₁ : a₁ ≡ 53 [ZMOD 64]) (ca₂ : a₂ ≡ 53 [ZMOD 64]) (cz : z₁ ≡ 41 [ZMOD 64])
    (ch : h ≡ 54 [ZMOD 64]) (cw : w ≡ 52 [ZMOD 64]) (hq : 0 < q → 90 ≤ q)
    (na₁ : a₁ < 0 → a₁ ≤ -75) (na₂ : a₂ < 0 → a₂ ≤ -75) (nh : h < 0 → h ≤ -138)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ z₁.natAbs ∨ p ∣ h.natAbs) →
      (p : ℤ) ≤ |x| + 1 ∧ (p : ℤ) ≤ |w| + 1)
    (hdeg : 8 * x + 4 * q = 0) (hpos : 0 < (72 : ℚ) / x + 400 / q)
    (hE₁ : (1 : ℚ) + 18 / x - 81 / z₁ + 36 / h - 16 / w = 0)
    (hE₂ : (2 : ℚ) - 18 / x - 200 / q + 25 / a₁ + 25 / a₂ + 108 / h - 16 / w = 0)
    (hL₁ : 1 + 2 * x - z₁ + h - w = 0)
    (hL₂ : 1 - 4 * x - 2 * q + a₁ + a₂ + z₁ + 2 * h = 0) : False := by
  obtain ⟨hq2, hx77, hqinv⟩ := lyons_four_cycle_le_neg_77 cx hq hdeg hpos
  have hL₂' : 1 + a₁ + a₂ + z₁ + 2 * h = 0 := by rw [hq2] at hL₂; linarith
  simp only [Int.ModEq] at cx ca₁ ca₂ cz ch cw
  have ba₁ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := a₁)
    (by rcases lt_or_ge a₁ 0 with h' | h'
        · exact Or.inr (na₁ h')
        · left; clear * - ca₁ h'; omega)
  have ba₂ := inv_mem_of_le_or_le (A := 53) (B := 75) (by norm_num) (by norm_num) (x := a₂)
    (by rcases lt_or_ge a₂ 0 with h' | h'
        · exact Or.inr (na₂ h')
        · left; clear * - ca₂ h'; omega)
  have bh := inv_mem_of_le_or_le (A := 54) (B := 138) (by norm_num) (by norm_num) (x := h)
    (by rcases lt_or_ge h 0 with h' | h'
        · exact Or.inr (nh h')
        · left; clear * - ch h'; omega)
  have bw := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w)
    (by clear * - cw; omega)
  push_cast at ba₁ ba₂ bh bw
  simp only [div_eq_mul_inv, hqinv] at hE₁ hE₂
  have hE₂' : 2 + 82 * (x : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 108 * (h : ℚ)⁻¹ -
      16 * (w : ℚ)⁻¹ = 0 := by linarith
  have hD : 1 + 64 * (x : ℚ)⁻¹ + 25 * (a₁ : ℚ)⁻¹ + 25 * (a₂ : ℚ)⁻¹ + 72 * (h : ℚ)⁻¹ +
      81 * (z₁ : ℚ)⁻¹ = 0 := by linarith
  by_cases hx : x = -77
  · subst hx
    push_cast at hE₁ hE₂' hD
    exact lyons_B_neg77 a₁ a₂ z₁ h w ca₁ ca₂ cz cw na₁ na₂ nh (fun p hp' hd => (hp p hp' hd).2)
      ba₁.1 ba₂.1 bh.1 bw.2 hE₁ hE₂' hD hL₁ hL₂'
  · have hsign : 0 < w → 0 < a₁ ∨ 0 < a₂ ∨ 0 < h := by
      intro hw
      by_contra hc
      simp only [not_or, not_lt] at hc
      clear * - hc hw hL₁ hL₂' hx77
      omega
    exact lyons_B_le141 x a₁ a₂ z₁ h w cx ca₁ ca₂ ch cw na₁ na₂ nh
      (by clear * - hx77 hx cx; omega) (fun p hp' hd => (hp p hp' hd).1) ba₁.1 ba₂.1 bh.1 bw.2
      hsign hE₂' hD hL₁ hL₂'

private theorem inv_cast_pos {y : ℤ} (hy : 0 < y) : (0 : ℚ) < (y : ℚ)⁻¹ :=
  inv_pos.mpr (by exact_mod_cast hy)

private theorem inv_cast_neg {y : ℤ} (hy : y < 0) : (y : ℚ)⁻¹ < 0 :=
  inv_lt_zero.mpr (by exact_mod_cast hy)

theorem lyons_J_arithmetic (x z₁ h y w : ℤ) (hy : 12 ≤ |y|) (cx : x ≡ 51 [ZMOD 64])
    (cz : z₁ ≡ 39 [ZMOD 64]) (ch : h ≡ 38 [ZMOD 64]) (cy : y ≡ 1 [ZMOD 64])
    (cw : w ≡ 52 [ZMOD 64]) (ph : 0 < h → 102 ≤ h)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ x.natAbs ∨ p ∣ z₁.natAbs) →
      (p : ℤ) ≤ |x| + 1 ∧ (p : ℤ) ≤ |z₁| + 1 ∧ (p : ℤ) ≤ |h| + 1 ∧ (p : ℤ) ≤ |y| + 1 ∧
        (p : ℤ) ≤ |w| + 1)
    (hE : (1 : ℚ) + 9 / x - 49 / z₁ + 36 / h + 1 / y - 16 / w = 0)
    (hL : 1 + x - z₁ + h + y - w = 0) (hR : x + z₁ + h = 0)
    (hP : 0 < -(4 : ℚ) + 392 / z₁ - 4 / y + 64 / w) : False := by
  simp only [Int.ModEq] at cx cz ch cy cw
  have hy' := le_abs'.mp hy
  have by' := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy hy'; omega)
  have bw := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w)
    (by clear * - cw; omega)
  push_cast at by' bw
  simp only [div_eq_mul_inv] at hE hP
  have hzpos : 0 < z₁ := by
    by_contra hz
    have hzn : z₁ < 0 := by clear * - hz cz; omega
    linarith [inv_cast_neg hzn, by'.1, bw.2]
  have hz167 : z₁ < 167 := by
    by_contra hz
    have := inv_pos_le_of_le (A := 167) (by norm_num) (x := z₁) (by omega)
    push_cast at this
    linarith [this.2, by'.1, bw.2]
  have hz : z₁ = 39 ∨ z₁ = 103 := by clear * - hzpos hz167 cz; omega
  rcases hz with hz | hz
  ·
    subst hz
    push_cast at hE
    have hh : h = -x - 39 := by omega
    have hp40 : ∀ p : ℕ, p.Prime → p ∣ x.natAbs → (p : ℤ) ≤ 40 := fun p hpp hd => by
      have := (hp p hpp (Or.inl hd)).2.1
      norm_num at this
      exact_mod_cast this
    have hcx : x = -13 ∨ 51 ≤ x ∨ x ≤ -77 := by clear * - cx; omega
    rcases hcx with hx | hx | hx
    ·
      subst hx
      have hh' : h = -26 := by omega
      subst hh'
      push_cast at hE
      have hwneg : (w : ℚ)⁻¹ < 0 := by linarith [by'.2]
      have hw : w < 0 := by
        have : (w : ℚ) < 0 := inv_lt_zero.mp hwneg
        exact_mod_cast this
      by_cases hw12 : w = -12
      · subst hw12
        push_cast at hE
        linarith [by'.2]
      · have := inv_neg_ge_of_le (B := 76) (by norm_num) (x := w)
          (by clear * - hw hw12 cw; omega)
        push_cast at this
        linarith [by'.2, this.1]
    ·
      have hhneg : h ≤ -90 := by omega
      have bh := inv_neg_ge_of_le (B := 90) (by norm_num) hhneg
      push_cast at bh
      have bx := inv_pos_le_of_le (A := 51) (by norm_num) hx
      push_cast at bx
      have hF : 9 * (x : ℚ)⁻¹ + 36 * (h : ℚ)⁻¹ < 0 := by
        have hx' : (51 : ℚ) ≤ x := by exact_mod_cast hx
        have hhq : (h : ℚ) = -((x : ℚ) + 39) := by rw [hh]; push_cast; ring
        rw [hhq, inv_neg]
        have : 9 * (x : ℚ)⁻¹ < 36 * ((x : ℚ) + 39)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv,
            div_lt_div_iff₀ (by linarith) (by linarith)]
          nlinarith
        linarith
      rcases lt_or_gt_of_ne (show w ≠ 0 by clear * - cw; omega) with hw | hw
      · by_cases hw12 : w = -12
        · subst hw12
          push_cast at hE
          linarith [by'.1, bx.1, bh.1]
        · have := inv_neg_ge_of_le (B := 76) (by norm_num) (x := w)
            (by clear * - hw hw12 cw; omega)
          push_cast at this
          linarith [by'.2, this.1]
      · linarith [by'.2, inv_cast_pos hw]
    ·
      have hhpos : 0 < h := by omega
      have h102 := ph hhpos
      have hx141 : x ≤ -141 := by omega
      have n141 : x ≠ -141 := by
        rintro rfl
        have := hp40 47 (by norm_num) (by decide)
        norm_num at this
      have n205 : x ≠ -205 := by
        rintro rfl
        have := hp40 41 (by norm_num) (by decide)
        norm_num at this
      have n269 : x ≠ -269 := by
        rintro rfl
        have := hp40 269 (by norm_num) (by decide)
        norm_num at this
      have hx333 : x ≤ -333 := by clear * - hx141 n141 n205 n269 cx; omega
      have bx := inv_neg_ge_of_le (B := 333) (by norm_num) hx333
      have bh := inv_pos_le_of_le (A := 294) (by norm_num) (x := h) (by omega)
      push_cast at bx bh
      rcases lt_or_gt_of_ne (show w ≠ 0 by clear * - cw; omega) with hw | hw
      · have hup : (w : ℚ)⁻¹ < -(1 / 140) := by linarith [by'.2]
        obtain ⟨-, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
        have hgt' : -140 < w := by
          have : (-140 : ℚ) < w := by norm_num at hgt; linarith
          exact_mod_cast this
        have hw' : w = -12 ∨ w = -76 := by clear * - hgt' hw cw; omega
        rcases hw' with hw' | hw'
        · subst hw'
          push_cast at hE
          linarith [by'.1]
        · subst hw'
          have : y = 1 := by omega
          subst this
          norm_num at hy
      · linarith [by'.2, inv_cast_pos hw]
  ·
    subst hz
    push_cast at hE
    obtain ⟨p₁, -, p₃, p₄, p₅⟩ := hp 103 (by norm_num) (Or.inr (by decide))
    push_cast at p₁ p₃ p₄ p₅
    have bx := inv_mem_of_le_or_le (A := 115) (B := 141) (by norm_num) (by norm_num) (x := x)
      (by rcases le_abs'.mp (by linarith : (102 : ℤ) ≤ |x|) with h' | h' <;>
        [right; left] <;> clear * - h' cx <;> omega)
    have bh := inv_mem_of_le_or_le (A := 102) (B := 154) (by norm_num) (by norm_num) (x := h)
      (by rcases le_abs'.mp (by linarith : (102 : ℤ) ≤ |h|) with h' | h' <;>
        [right; left] <;> clear * - h' ch <;> omega)
    have by'' := inv_mem_of_le_or_le (A := 129) (B := 127) (by norm_num) (by norm_num) (x := y)
      (by rcases le_abs'.mp (by linarith : (102 : ℤ) ≤ |y|) with h' | h' <;>
        [right; left] <;> clear * - h' cy <;> omega)
    have bw' := inv_mem_of_le_or_le (A := 116) (B := 140) (by norm_num) (by norm_num) (x := w)
      (by rcases le_abs'.mp (by linarith : (102 : ℤ) ≤ |w|) with h' | h' <;>
        [right; left] <;> clear * - h' cw <;> omega)
    push_cast at bx bh by'' bw'
    linarith [bx.1, bh.1, by''.1, bw'.2]

private theorem lyons_K_final (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hE : 9 * (x : ℚ)⁻¹ + (y : ℚ)⁻¹ = -(172 / 9009)) (hL : x + y = 372) : False := by
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have h1 : (x : ℚ) * (x : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hx'
  have h2 : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy'
  have hmul : 9 * (y : ℚ) + x = -(172 / 9009) * (x * y) := by
    linear_combination (↑x * ↑y) * hE - 9 * ↑y * h1 - ↑x * h2
  have hL' : (x : ℚ) + y = 372 := by exact_mod_cast hL
  have key : 43 * (x : ℚ) ^ 2 + 2022 * x - 7540533 = 0 := by
    linear_combination (-(9009 / 4 : ℚ)) * hmul + (43 * (↑x : ℚ) + 81081 / 4) * hL'
  have keyZ : 43 * x ^ 2 + 2022 * x - 7540533 = 0 := by exact_mod_cast key
  have hsq : (86 * x + 2022) ^ 2 = 1301060160 := by linear_combination 172 * keyZ
  rcases le_or_gt (86 * x + 2022) 36070 with h1 | h1
  · rcases le_or_gt (-36070) (86 * x + 2022) with h2 | h2
    · have := sq_le_sq' h2 h1
      linarith
    · have hw : (36071 : ℤ) ≤ -(86 * x + 2022) := by omega
      have := pow_le_pow_left₀ (by norm_num) hw 2
      rw [neg_sq] at this
      linarith
  · have hw : (36071 : ℤ) ≤ 86 * x + 2022 := by omega
    have := pow_le_pow_left₀ (by norm_num) hw 2
    linarith

private theorem le_neg_511 {y : ℤ} (cy : y % 64 = 1 % 64) (hy : y < 0) (hy12 : y ≤ -12)
    (h63 : y ≠ -63) (hp : ∀ p : ℕ, p.Prime → p ∣ y.natAbs → (p : ℤ) ≤ 14) : y ≤ -511 := by
  have ex : ∀ p : ℕ, p.Prime → 14 < p → ¬ (p ∣ y.natAbs) := fun p hpp hlt hd => by
    have := hp p hpp hd
    omega
  have n127 : y ≠ -127 := by rintro rfl; exact ex 127 (by norm_num) (by norm_num) (by decide)
  have n191 : y ≠ -191 := by rintro rfl; exact ex 191 (by norm_num) (by norm_num) (by decide)
  have n255 : y ≠ -255 := by rintro rfl; exact ex 17 (by norm_num) (by norm_num) (by decide)
  have n319 : y ≠ -319 := by rintro rfl; exact ex 29 (by norm_num) (by norm_num) (by decide)
  have n383 : y ≠ -383 := by rintro rfl; exact ex 383 (by norm_num) (by norm_num) (by decide)
  have n447 : y ≠ -447 := by rintro rfl; exact ex 149 (by norm_num) (by norm_num) (by decide)
  clear * - cy hy hy12 h63 n127 n191 n255 n319 n383 n447
  omega

private theorem lyons_K_core (x₂ z₁ y₁ y₂ : ℤ) (hy₁ : y₁ ≤ -12 ∨ 12 ≤ y₁)
    (hy₂ : y₂ ≤ -12 ∨ 12 ≤ y₂) (c₂ : x₂ % 64 = 51 % 64) (cz : z₁ % 64 = 41 % 64)
    (d₁ : y₁ % 64 = 1 % 64) (d₂ : y₂ % 64 = 1 % 64) (n₂ : x₂ ≠ -13)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ x₂.natAbs ∨ p ∣ z₁.natAbs ∨ p ∣ y₁.natAbs ∨ p ∣ y₂.natAbs) →
      (p : ℤ) ≤ 14)
    (hE : 1 + 9 * (-13 : ℚ)⁻¹ + 9 * (x₂ : ℚ)⁻¹ - 81 * (z₁ : ℚ)⁻¹ + (y₁ : ℚ)⁻¹ + (y₂ : ℚ)⁻¹ = 0)
    (hL : 1 + (-13) + x₂ - z₁ + y₁ + y₂ = 0) : False := by
  have b₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₁)
    (by clear * - d₁ hy₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₂)
    (by clear * - d₂ hy₂; omega)
  have bx := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ n₂; omega)
  push_cast at b₁ b₂ bx
  have hlow : (1 / 540 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1, bx.1]
  obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hzlt' : z₁ < 540 := by
    have : (z₁ : ℚ) < 540 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have n51 : x₂ ≠ 51 := by
    rintro rfl
    have := hp 17 (by norm_num) (Or.inl (by decide))
    norm_num at this
  have bx' := inv_mem_of_le_or_le (A := 115) (B := 77) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ n₂ n51; omega)
  push_cast at bx'
  have hup : (z₁ : ℚ)⁻¹ < 1 / 169 := by linarith [b₁.2, b₂.2, bx'.2]
  have hz169 : 169 < z₁ := by
    by_contra hz
    have h' := inv_anti₀ (by exact_mod_cast hzpos : (0 : ℚ) < z₁)
      (by exact_mod_cast (by omega : z₁ ≤ 169) : (z₁ : ℚ) ≤ 169)
    rw [one_div] at hup
    linarith
  have ex : ∀ p : ℕ, p.Prime → 14 < p → ¬ (p ∣ z₁.natAbs) := fun p hpp hlt hd => by
    have := hp p hpp (Or.inr (Or.inl hd))
    omega
  have n233 : z₁ ≠ 233 := by rintro rfl; exact ex 233 (by norm_num) (by norm_num) (by decide)
  have n361 : z₁ ≠ 361 := by rintro rfl; exact ex 19 (by norm_num) (by norm_num) (by decide)
  have n425 : z₁ ≠ 425 := by rintro rfl; exact ex 17 (by norm_num) (by norm_num) (by decide)
  have n489 : z₁ ≠ 489 := by rintro rfl; exact ex 163 (by norm_num) (by norm_num) (by decide)
  have hz : z₁ = 297 := by
    clear * - hz169 hzlt' cz n233 n361 n425 n489
    omega
  subst hz
  push_cast at hE
  have hE' : 9 * (x₂ : ℚ)⁻¹ + (y₁ : ℚ)⁻¹ + (y₂ : ℚ)⁻¹ = -(5 / 143) := by linarith
  have far : ∀ y : ℤ, y % 64 = 1 % 64 → (y ≤ -12 ∨ 12 ≤ y) → y ≠ -63 →
      (∀ p : ℕ, p.Prime → p ∣ y.natAbs → (p : ℤ) ≤ 14) → -(1 / 500 : ℚ) < (y : ℚ)⁻¹ := by
    intro y cy hy h63 hpy
    rcases lt_or_gt_of_ne (show y ≠ 0 by clear * - cy; omega) with hyn | hyp
    · have h511 := le_neg_511 cy hyn (by omega) h63 hpy
      have := inv_neg_ge_of_le (B := 511) (by norm_num) h511
      push_cast at this
      linarith [this.1]
    · linarith [inv_cast_pos hyp]
  by_cases m₁ : y₁ = -63
  · subst m₁
    push_cast at hE'
    exact lyons_K_final x₂ y₂ (by clear * - c₂; omega) (by clear * - d₂; omega)
      (by linarith) (by linarith)
  · by_cases m₂ : y₂ = -63
    · subst m₂
      push_cast at hE'
      exact lyons_K_final x₂ y₁ (by clear * - c₂; omega) (by clear * - d₁; omega)
        (by linarith) (by linarith)
    · have f₁ := far y₁ d₁ hy₁ m₁ fun p hpp hd => hp p hpp (Or.inr (Or.inr (Or.inl hd)))
      have f₂ := far y₂ d₂ hy₂ m₂ fun p hpp hd => hp p hpp (Or.inr (Or.inr (Or.inr hd)))
      have hxup : (x₂ : ℚ)⁻¹ < -(123 / 35750) := by linarith
      obtain ⟨hxneg, hxgt⟩ := neg_gt_of_inv_lt (by norm_num) hxup
      have hxgt' : -291 < x₂ := by
        have : (-291 : ℚ) < x₂ := by norm_num at hxgt; linarith
        exact_mod_cast this
      have ex' : ∀ p : ℕ, p.Prime → 14 < p → ¬ (p ∣ x₂.natAbs) := fun p hpp hlt hd => by
        have := hp p hpp (Or.inl hd)
        omega
      have n141 : x₂ ≠ -141 := by rintro rfl; exact ex' 47 (by norm_num) (by norm_num) (by decide)
      have n205 : x₂ ≠ -205 := by rintro rfl; exact ex' 41 (by norm_num) (by norm_num) (by decide)
      have n269 : x₂ ≠ -269 := by
        rintro rfl; exact ex' 269 (by norm_num) (by norm_num) (by decide)
      have hx77 : x₂ = -77 := by
        clear * - hxneg hxgt' c₂ n₂ n141 n205 n269
        omega
      subst hx77
      push_cast at hE'
      linarith [b₁.2, b₂.2]

theorem lyons_K_arithmetic (x₁ x₂ q z₁ y₁ y₂ : ℤ) (hy₁ : 12 ≤ |y₁|) (hy₂ : 12 ≤ |y₂|)
    (c₁ : x₁ ≡ 51 [ZMOD 64]) (c₂ : x₂ ≡ 51 [ZMOD 64]) (cz : z₁ ≡ 41 [ZMOD 64])
    (d₁ : y₁ ≡ 1 [ZMOD 64]) (d₂ : y₂ ≡ 1 [ZMOD 64]) (hq : 0 < q → 90 ≤ q)
    (hp : x₁ ≠ x₂ → ∀ p : ℕ, p.Prime → (p ∣ x₁.natAbs ∨ p ∣ x₂.natAbs ∨ p ∣ z₁.natAbs ∨
      p ∣ y₁.natAbs ∨ p ∣ y₂.natAbs) → (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1)
    (hE : (1 : ℚ) + 9 / x₁ + 9 / x₂ - 81 / z₁ + 1 / y₁ + 1 / y₂ = 0)
    (hL : 1 + x₁ + x₂ - z₁ + y₁ + y₂ = 0) (hR : q = -(x₁ + x₂))
    (hP : 0 < (36 : ℚ) / x₁ + 36 / x₂ + 400 / q) : False := by
  by_cases heq : x₁ = x₂
  · subst heq
    refine lyons_ADG_arithmetic x₁ q y₁ y₂ z₁ hy₁ hy₂ c₁ d₁ d₂ cz hq (by omega) ?_ (by omega) ?_
    · have : (72 : ℚ) / x₁ = 36 / x₁ + 36 / x₁ := by ring
      linarith
    · have : (18 : ℚ) / x₁ = 9 / x₁ + 9 / x₁ := by ring
      linarith
  have hp' := hp heq
  have hy₁' := le_abs'.mp hy₁
  have hy₂' := le_abs'.mp hy₂
  simp only [Int.ModEq] at c₁ c₂ cz d₁ d₂
  simp only [div_eq_mul_inv] at hE
  by_cases m₁ : x₁ = -13
  · subst m₁
    push_cast at hE
    refine lyons_K_core x₂ z₁ y₁ y₂ hy₁' hy₂' c₂ cz d₁ d₂ (fun h => heq h.symm)
      (fun p hpp hd => ?_) (by linarith) (by linarith)
    have := (hp' p hpp (Or.inr hd)).1
    norm_num at this
    exact_mod_cast this
  by_cases m₂ : x₂ = -13
  · subst m₂
    push_cast at hE
    refine lyons_K_core x₁ z₁ y₁ y₂ hy₁' hy₂' c₁ cz d₁ d₂ m₁
      (fun p hpp hd => ?_) (by linarith) (by linarith)
    have := (hp' p hpp (by rcases hd with hd | hd <;> simp only [hd, true_or, or_true])).2
    norm_num at this
    exact_mod_cast this
  have b₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₁)
    (by clear * - d₁ hy₁'; omega)
  have b₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₂)
    (by clear * - d₂ hy₂'; omega)
  have bx₁ := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ m₁; omega)
  have bx₂ := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ m₂; omega)
  push_cast at b₁ b₂ bx₁ bx₂
  have hsum : -(9 / 77 + 9 / 141 : ℚ) ≤ 9 * (x₁ : ℚ)⁻¹ + 9 * (x₂ : ℚ)⁻¹ := by
    by_cases h77 : x₁ = -77
    · have := inv_mem_of_le_or_le (A := 51) (B := 141) (by norm_num) (by norm_num) (x := x₂)
        (by clear * - c₂ m₂ h77 heq; omega)
      push_cast at this
      linarith [this.1, bx₁.1]
    · have := inv_mem_of_le_or_le (A := 51) (B := 141) (by norm_num) (by norm_num) (x := x₁)
        (by clear * - c₁ m₁ h77; omega)
      push_cast at this
      linarith [this.1, bx₂.1]
  have hlow : (1 / 105 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [b₁.1, b₂.1]
  have hup : (z₁ : ℚ)⁻¹ < 1 / 41 := by linarith [b₁.2, b₂.2, bx₁.2, bx₂.2]
  obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hzlt' : z₁ < 105 := by
    have : (z₁ : ℚ) < 105 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have hz : z₁ = 41 := by clear * - hzpos hzlt' cz; omega
  subst hz
  norm_num at hup

private theorem lyons_L_final (y w : ℤ) (hy : y ≠ 0) (hw : w ≠ 0)
    (hE : (y : ℚ)⁻¹ - 16 * (w : ℚ)⁻¹ = 9 / 77) (hL : y - w = 141) : False := by
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hw' : (w : ℚ) ≠ 0 := by exact_mod_cast hw
  have h1 : (y : ℚ) * (y : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hy'
  have h2 : (w : ℚ) * (w : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hw'
  have hmul : (w : ℚ) - 16 * y - 9 / 77 * (y * w) = 0 := by
    linear_combination (↑y * ↑w) * hE - ↑w * h1 + 16 * ↑y * h2
  have hL' : (y : ℚ) - w - 141 = 0 := by
    have : ((y - w : ℤ) : ℚ) = 141 := by exact_mod_cast hL
    push_cast at this
    linarith
  have key : 9 * (w : ℚ) ^ 2 + 2424 * w + 173712 = 0 := by
    linear_combination (-77 : ℚ) * hmul + (-9 * (↑w : ℚ) - 1232) * hL'
  nlinarith [sq_nonneg (3 * (w : ℚ) + 404)]

private theorem ge_180 {w : ℤ} (cw : w % 64 = 52 % 64) (hw : 0 < w) (h52 : w ≠ 52)
    (hp : ∀ p : ℕ, p.Prime → p ∣ w.natAbs → (p : ℤ) ≤ 14) : 180 ≤ w := by
  have n116 : w ≠ 116 := by
    rintro rfl
    have := hp 29 (by norm_num) (by decide)
    norm_num at this
  clear * - cw hw h52 n116
  omega

private theorem lyons_L_core (x₂ q y w₁ w₂ : ℤ) (hy : y ≤ -12 ∨ 12 ≤ y)
    (c₂ : x₂ % 64 = 51 % 64) (cq : q % 64 = 26 % 64) (cy : y % 64 = 1 % 64)
    (d₁ : w₁ % 64 = 52 % 64) (d₂ : w₂ % 64 = 52 % 64) (hq : 0 < q → 90 ≤ q)
    (hp : x₂ ≠ -13 → ∀ p : ℕ, p.Prime → (p ∣ w₁.natAbs ∨ p ∣ w₂.natAbs) → (p : ℤ) ≤ 14)
    (hE : 1 + 9 * (-13 : ℚ)⁻¹ + 9 * (x₂ : ℚ)⁻¹ + (y : ℚ)⁻¹ - 16 * (w₁ : ℚ)⁻¹ -
      16 * (w₂ : ℚ)⁻¹ = 0)
    (hL : 1 + (-13) + x₂ + y - w₁ - w₂ = 0) (hR : q = -(-13 + x₂))
    (hP : 0 < 36 * (-13 : ℚ)⁻¹ + 36 * (x₂ : ℚ)⁻¹ + 400 * (q : ℚ)⁻¹) : False := by
  have n₂ : x₂ ≠ -13 := by
    rintro rfl
    have := hq (by omega)
    omega
  have hp' := hp n₂
  have by' := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy hy; omega)
  have b₁ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₁)
    (by clear * - d₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₂)
    (by clear * - d₂; omega)
  push_cast at by' b₁ b₂
  have hxneg : x₂ < 0 := by
    by_contra hx
    have hx51 : 51 ≤ x₂ := by clear * - hx c₂; omega
    have bx := inv_pos_le_of_le (A := 51) (by norm_num) hx51
    push_cast at bx
    have hqneg : q < 0 := by omega
    linarith [bx.2, inv_cast_neg hqneg]
  have hx77 : x₂ ≤ -77 := by clear * - hxneg c₂ n₂; omega
  have hqpos : 0 < q := by omega
  have hq90 := hq hqpos
  have hlow : (9 / 1300 : ℚ) < (q : ℚ)⁻¹ := by linarith [inv_cast_neg hxneg]
  obtain ⟨-, hqlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hqlt' : q < 145 := by
    have : (q : ℚ) < 145 := by norm_num at hqlt; linarith
    exact_mod_cast this
  have hq' : q = 90 := by clear * - hq90 hqlt' cq; omega
  have hx' : x₂ = -77 := by omega
  subst hx'
  push_cast at hE
  have big : ∀ w : ℤ, w % 64 = 52 % 64 → w ≠ 52 → (w = w₁ ∨ w = w₂) → w < 0 ∨ 180 ≤ w := by
    intro w cw h52 hw
    rcases lt_or_gt_of_ne (show w ≠ 0 by clear * - cw; omega) with h | h
    · exact Or.inl h
    · refine Or.inr (ge_180 cw h h52 fun p hpp hd => hp' p hpp ?_)
      rcases hw with rfl | rfl
      · exact Or.inl hd
      · exact Or.inr hd
  have hy0 : y ≠ 0 := by clear * - cy; omega
  by_cases m₁ : w₁ = 52
  · subst m₁
    push_cast at hE
    exact lyons_L_final y w₂ hy0 (by clear * - d₂; omega) (by linarith) (by linarith)
  by_cases m₂ : w₂ = 52
  · subst m₂
    push_cast at hE
    exact lyons_L_final y w₁ hy0 (by clear * - d₁; omega) (by linarith) (by linarith)
  have far : ∀ w : ℤ, 180 ≤ w → (w : ℚ)⁻¹ ≤ 1 / 180 := fun w hw => by
    have := inv_pos_le_of_le (A := 180) (by norm_num) hw
    push_cast at this
    exact this.2
  rcases big w₁ d₁ m₁ (Or.inl rfl) with h₁ | h₁ <;>
    rcases big w₂ d₂ m₂ (Or.inr rfl) with h₂ | h₂
  · linarith [inv_cast_neg h₁, inv_cast_neg h₂, by'.1]
  · linarith [inv_cast_neg h₁, far w₂ h₂, by'.1]
  · linarith [far w₁ h₁, inv_cast_neg h₂, by'.1]
  · have hypos : 0 < y := by omega
    linarith [far w₁ h₁, far w₂ h₂, inv_cast_pos hypos]

theorem lyons_L_arithmetic (x₁ x₂ q y w₁ w₂ : ℤ) (hy : 12 ≤ |y|) (c₁ : x₁ ≡ 51 [ZMOD 64])
    (c₂ : x₂ ≡ 51 [ZMOD 64]) (cq : q ≡ 26 [ZMOD 64]) (cy : y ≡ 1 [ZMOD 64])
    (d₁ : w₁ ≡ 52 [ZMOD 64]) (d₂ : w₂ ≡ 52 [ZMOD 64]) (hq : 0 < q → 90 ≤ q)
    (hp : x₁ ≠ x₂ → ∀ p : ℕ, p.Prime → (p ∣ w₁.natAbs ∨ p ∣ w₂.natAbs) →
      (p : ℤ) ≤ |x₁| + 1 ∧ (p : ℤ) ≤ |x₂| + 1)
    (hE : (1 : ℚ) + 9 / x₁ + 9 / x₂ + 1 / y - 16 / w₁ - 16 / w₂ = 0)
    (hL : 1 + x₁ + x₂ + y - w₁ - w₂ = 0) (hR : q = -(x₁ + x₂))
    (hP : 0 < (36 : ℚ) / x₁ + 36 / x₂ + 400 / q) : False := by
  have hy' := le_abs'.mp hy
  simp only [Int.ModEq] at c₁ c₂ cq cy d₁ d₂
  simp only [div_eq_mul_inv] at hE hP
  by_cases m₁ : x₁ = -13
  · subst m₁
    push_cast at hE hP
    refine lyons_L_core x₂ q y w₁ w₂ hy' c₂ cq cy d₁ d₂ hq (fun hne p hpp hd => ?_)
      (by linarith) hL hR hP
    have := (hp (fun h => hne h.symm) p hpp hd).1
    norm_num at this
    exact_mod_cast this
  by_cases m₂ : x₂ = -13
  · subst m₂
    push_cast at hE hP
    refine lyons_L_core x₁ q y w₁ w₂ hy' c₁ cq cy d₁ d₂ hq (fun hne p hpp hd => ?_)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have := (hp hne p hpp hd).2
    norm_num at this
    exact_mod_cast this
  have by' := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y)
    (by clear * - cy hy'; omega)
  have b₁ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₁)
    (by clear * - d₁; omega)
  have b₂ := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := w₂)
    (by clear * - d₂; omega)
  have bx₁ := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ m₁; omega)
  have bx₂ := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ m₂; omega)
  push_cast at by' b₁ b₂ bx₁ bx₂
  linarith [by'.1, b₁.2, b₂.2, bx₁.1, bx₂.1]

private theorem lyons_N_core (x₁ x₂ h₂ q z₁ y₁ y₂ : ℤ)
    (bx₁ : -(1 / 63 : ℚ) ≤ (x₁ : ℚ)⁻¹ ∧ (x₁ : ℚ)⁻¹ ≤ 1 / 65)
    (bx₂ : -(1 / 63 : ℚ) ≤ (x₂ : ℚ)⁻¹ ∧ (x₂ : ℚ)⁻¹ ≤ 1 / 65)
    (by₁ : -(1 / 63 : ℚ) ≤ (y₁ : ℚ)⁻¹ ∧ (y₁ : ℚ)⁻¹ ≤ 1 / 65)
    (by₂ : -(1 / 63 : ℚ) ≤ (y₂ : ℚ)⁻¹ ∧ (y₂ : ℚ)⁻¹ ≤ 1 / 65)
    (e₂ : h₂ % 64 = 52 % 64) (cq : q % 64 = 26 % 64) (cz : z₁ % 64 = 41 % 64)
    (hq154 : 0 < q → 154 ≤ q) (nz : z₁ < 0 → z₁ ≤ -87)
    (hp : h₂ ≠ -12 → ∀ p : ℕ, p.Prime → (p ∣ h₂.natAbs ∨ p ∣ q.natAbs) → (p : ℤ) ≤ 13)
    (hE₁ : 1 + 4 * (x₁ : ℚ)⁻¹ + 4 * (x₂ : ℚ)⁻¹ - 200 * (q : ℚ)⁻¹ + (y₁ : ℚ)⁻¹ + (y₂ : ℚ)⁻¹ +
      81 * (z₁ : ℚ)⁻¹ = 0)
    (hE₂ : 2 + 3 * (x₁ : ℚ)⁻¹ + 3 * (x₂ : ℚ)⁻¹ + 16 * (-12 : ℚ)⁻¹ + 16 * (h₂ : ℚ)⁻¹ -
      200 * (q : ℚ)⁻¹ + 2 * (y₁ : ℚ)⁻¹ + 2 * (y₂ : ℚ)⁻¹ = 0) : False := by
  by_cases h12 : h₂ = -12
  ·
    subst h12
    push_cast at hE₂
    have hup : (z₁ : ℚ)⁻¹ < -(1 / 87) := by linarith [bx₁.1, bx₂.1, by₁.2, by₂.2]
    obtain ⟨hneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hgt' : -87 < z₁ := by
      have : (-87 : ℚ) < z₁ := by norm_num at hgt; linarith
      exact_mod_cast this
    have := nz hneg
    omega
  have hp' := hp h12
  have ex : ∀ p : ℕ, p.Prime → 13 < p → ¬ (p ∣ h₂.natAbs ∨ p ∣ q.natAbs) := fun p hpp hlt hd => by
    have := hp' p hpp hd
    omega
  have n76 : h₂ ≠ -76 := by
    rintro rfl
    exact ex 19 (by norm_num) (by norm_num) (Or.inl (by decide))
  have bh := inv_mem_of_le_or_le (A := 52) (B := 140) (by norm_num) (by norm_num) (x := h₂)
    (by clear * - e₂ h12 n76; omega)
  push_cast at bh
  have hq : q = 154 := by
    by_contra hne
    have hfar : -(200 : ℚ) * (q : ℚ)⁻¹ ≥ -(200 / 602) := by
      rcases lt_or_gt_of_ne (show q ≠ 0 by clear * - cq; omega) with hqn | hqp
      · linarith [inv_cast_neg hqn]
      · have h154 := hq154 hqp
        have n218 : q ≠ 218 := by
          rintro rfl; exact ex 109 (by norm_num) (by norm_num) (Or.inr (by decide))
        have n282 : q ≠ 282 := by
          rintro rfl; exact ex 47 (by norm_num) (by norm_num) (Or.inr (by decide))
        have n346 : q ≠ 346 := by
          rintro rfl; exact ex 173 (by norm_num) (by norm_num) (Or.inr (by decide))
        have n410 : q ≠ 410 := by
          rintro rfl; exact ex 41 (by norm_num) (by norm_num) (Or.inr (by decide))
        have n474 : q ≠ 474 := by
          rintro rfl; exact ex 79 (by norm_num) (by norm_num) (Or.inr (by decide))
        have n538 : q ≠ 538 := by
          rintro rfl; exact ex 269 (by norm_num) (by norm_num) (Or.inr (by decide))
        have h602 : 602 ≤ q := by
          clear * - h154 hne cq n218 n282 n346 n410 n474 n538
          omega
        have := inv_pos_le_of_le (A := 602) (by norm_num) h602
        push_cast at this
        linarith [this.2]
    linarith [bx₁.1, bx₂.1, by₁.1, by₂.1, bh.1]
  subst hq
  push_cast at hE₂
  have hlow : (1 / 52 : ℚ) < (h₂ : ℚ)⁻¹ := by linarith [bx₁.2, bx₂.2, by₁.2, by₂.2]
  obtain ⟨hpos, hlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hlt' : h₂ < 52 := by
    have : (h₂ : ℚ) < 52 := by norm_num at hlt; exact hlt
    exact_mod_cast this
  clear * - hpos hlt' e₂
  omega

theorem lyons_N_arithmetic (x₁ x₂ h₁ h₂ q z₁ y₁ y₂ : ℤ) (hx₁ : 12 ≤ |x₁|) (hx₂ : 12 ≤ |x₂|)
    (hy₁ : 12 ≤ |y₁|) (hy₂ : 12 ≤ |y₂|) (c₁ : x₁ ≡ 1 [ZMOD 64]) (c₂ : x₂ ≡ 1 [ZMOD 64])
    (d₁ : y₁ ≡ 1 [ZMOD 64]) (d₂ : y₂ ≡ 1 [ZMOD 64]) (e₁ : h₁ ≡ 52 [ZMOD 64])
    (e₂ : h₂ ≡ 52 [ZMOD 64]) (cq : q ≡ 26 [ZMOD 64]) (cz : z₁ ≡ 41 [ZMOD 64])
    (hq : 0 < q → 90 ≤ q) (nz : z₁ < 0 → z₁ ≤ -87)
    (hp : h₁ ≠ h₂ → ∀ p : ℕ, p.Prime → (p ∣ h₁.natAbs ∨ p ∣ h₂.natAbs ∨ p ∣ q.natAbs) →
      (p : ℤ) ≤ |h₁| + 1 ∧ (p : ℤ) ≤ |h₂| + 1)
    (hE₁ : (1 : ℚ) + 4 / x₁ + 4 / x₂ - 200 / q + 1 / y₁ + 1 / y₂ + 81 / z₁ = 0)
    (hE₂ : (2 : ℚ) + 3 / x₁ + 3 / x₂ + 16 / h₁ + 16 / h₂ - 200 / q + 2 / y₁ + 2 / y₂ = 0) :
    False := by
  simp only [Int.ModEq] at c₁ c₂ d₁ d₂ e₁ e₂ cq cz
  have bx₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₁)
    (by clear * - c₁ hx₁; rw [le_abs'] at hx₁; omega)
  have bx₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := x₂)
    (by clear * - c₂ hx₂; rw [le_abs'] at hx₂; omega)
  have by₁ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₁)
    (by clear * - d₁ hy₁; rw [le_abs'] at hy₁; omega)
  have by₂ := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := y₂)
    (by clear * - d₂ hy₂; rw [le_abs'] at hy₂; omega)
  have bz := inv_mem_of_le_or_le (A := 41) (B := 87) (by norm_num) (by norm_num) (x := z₁)
    (by rcases lt_or_ge z₁ 0 with h | h
        · exact Or.inr (nz h)
        · left; clear * - cz h; omega)
  push_cast at bx₁ bx₂ by₁ by₂ bz
  simp only [div_eq_mul_inv] at hE₁ hE₂
  have n90 : q ≠ 90 := by
    rintro rfl
    push_cast at hE₁
    have hlow : (1 / 105 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [bx₁.2, bx₂.2, by₁.2, by₂.2]
    have hup : (z₁ : ℚ)⁻¹ < 1 / 41 := by linarith [bx₁.1, bx₂.1, by₁.1, by₂.1]
    obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hzlt' : z₁ < 105 := by
      have : (z₁ : ℚ) < 105 := by norm_num at hzlt; exact hzlt
      exact_mod_cast this
    have hz : z₁ = 41 := by clear * - hzpos hzlt' cz; omega
    subst hz
    norm_num at hup
  have hq154 : 0 < q → 154 ≤ q := fun h => by
    have := hq h
    clear * - this n90 cq
    omega
  have bq := inv_mem_of_le_or_le (A := 154) (B := 38) (by norm_num) (by norm_num) (x := q)
    (by rcases lt_or_ge 0 q with h | h
        · exact Or.inl (hq154 h)
        · right; clear * - cq h; omega)
  push_cast at bq
  by_cases m₁ : h₁ = -12
  · subst m₁
    push_cast at hE₂
    refine lyons_N_core x₁ x₂ h₂ q z₁ y₁ y₂ bx₁ bx₂ by₁ by₂ e₂ cq cz hq154 nz
      (fun hne p hpp hd => ?_) (by linarith) (by linarith)
    have := (hp (fun h => hne h.symm) p hpp (by
      rcases hd with hd | hd <;> simp only [hd, true_or, or_true])).1
    norm_num at this
    exact_mod_cast this
  by_cases m₂ : h₂ = -12
  · subst m₂
    push_cast at hE₂
    refine lyons_N_core x₁ x₂ h₁ q z₁ y₁ y₂ bx₁ bx₂ by₁ by₂ e₁ cq cz hq154 nz
      (fun hne p hpp hd => ?_) (by linarith) (by linarith)
    have := (hp hne p hpp (by
      rcases hd with hd | hd <;> simp only [hd, true_or, or_true])).2
    norm_num at this
    exact_mod_cast this
  have bh₁ := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := h₁)
    (by clear * - e₁ m₁; omega)
  have bh₂ := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := h₂)
    (by clear * - e₂ m₂; omega)
  push_cast at bh₁ bh₂
  linarith [bx₁.1, bx₂.1, by₁.1, by₂.1, bh₁.1, bh₂.1, bq.2]

private theorem lyons_T_103 (x h k v w : ℤ) (cx : x % 64 = 51 % 64) (ch : h % 64 = 52 % 64)
    (ck : k % 64 = 1 % 64) (cw : w % 64 = 54 % 64)
    (p₁ : (102 : ℤ) ≤ |x|) (p₂ : (102 : ℤ) ≤ |h|) (p₃ : (102 : ℤ) ≤ |k|)
    (hE₁ : 2 - 18 * (x : ℚ)⁻¹ + 16 * (h : ℚ)⁻¹ + 3 * (k : ℚ)⁻¹ - 147 * (103 : ℚ)⁻¹ +
      108 * (w : ℚ)⁻¹ = 0)
    (hE₂ : 1 + 72 * (x : ℚ)⁻¹ + 32 * (h : ℚ)⁻¹ - 6 * (k : ℚ)⁻¹ - 243 * (v : ℚ)⁻¹ = 0)
    (hL : 1 - 2 * 103 - v + w = 0) : False := by
  have bx := inv_mem_of_le_or_le (A := 115) (B := 141) (by norm_num) (by norm_num) (x := x)
    (by rcases le_abs'.mp p₁ with h' | h' <;> [right; left] <;> clear * - h' cx <;> omega)
  have bh := inv_mem_of_le_or_le (A := 116) (B := 140) (by norm_num) (by norm_num) (x := h)
    (by rcases le_abs'.mp p₂ with h' | h' <;> [right; left] <;> clear * - h' ch <;> omega)
  have bk := inv_mem_of_le_or_le (A := 129) (B := 127) (by norm_num) (by norm_num) (x := k)
    (by rcases le_abs'.mp p₃ with h' | h' <;> [right; left] <;> clear * - h' ck <;> omega)
  push_cast at bx bh bk
  rcases lt_or_gt_of_ne (show w ≠ 0 by clear * - cw; omega) with hw | hw
  · have hv : v < 0 := by omega
    have hup : (x : ℚ)⁻¹ < -(1 / 108) := by linarith [bh.1, bk.2, inv_cast_neg hv]
    obtain ⟨hxneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hgt' : -108 < x := by
      have : (-108 : ℚ) < x := by norm_num at hgt; linarith
      exact_mod_cast this
    rcases le_abs'.mp p₁ with h' | h' <;> omega
  · linarith [bx.2, bh.1, bk.1, inv_cast_pos hw]

theorem lyons_T_arithmetic (x h k z₁ v w : ℤ) (hk : 12 ≤ |k|) (cx : x ≡ 51 [ZMOD 64])
    (ch : h ≡ 52 [ZMOD 64]) (ck : k ≡ 1 [ZMOD 64]) (cz : z₁ ≡ 39 [ZMOD 64])
    (cv : v ≡ 41 [ZMOD 64]) (cw : w ≡ 54 [ZMOD 64]) (nv : v < 0 → v ≤ -87)
    (nw : w < 0 → w ≤ -138)
    (hp : ∀ p : ℕ, p.Prime → (p ∣ z₁.natAbs ∨ p ∣ v.natAbs) →
      (p : ℤ) ≤ |x| + 1 ∧ (p : ℤ) ≤ |h| + 1 ∧ (p : ℤ) ≤ |k| + 1 ∧ (p : ℤ) ≤ |w| + 1)
    (hE₁ : (2 : ℚ) - 18 / x + 16 / h + 3 / k - 147 / z₁ + 108 / w = 0)
    (hE₂ : (1 : ℚ) + 72 / x + 32 / h - 6 / k - 243 / v = 0)
    (hL : 1 - 2 * z₁ - v + w = 0)
    (hP : 0 < (1 : ℚ) + 36 / x + 64 / h + 98 / z₁ + 81 / v + 72 / w) : False := by
  simp only [Int.ModEq] at cx ch ck cz cv cw
  have hk' := le_abs'.mp hk
  have bx := inv_mem_of_le_or_le (A := 51) (B := 13) (by norm_num) (by norm_num) (x := x)
    (by clear * - cx; omega)
  have bh := inv_mem_of_le_or_le (A := 52) (B := 12) (by norm_num) (by norm_num) (x := h)
    (by clear * - ch; omega)
  have bk := inv_mem_of_le_or_le (A := 65) (B := 63) (by norm_num) (by norm_num) (x := k)
    (by clear * - ck hk'; omega)
  have bv := inv_mem_of_le_or_le (A := 41) (B := 87) (by norm_num) (by norm_num) (x := v)
    (by rcases lt_or_ge v 0 with h' | h'
        · exact Or.inr (nv h')
        · left; clear * - cv h'; omega)
  have bw := inv_mem_of_le_or_le (A := 54) (B := 138) (by norm_num) (by norm_num) (x := w)
    (by rcases lt_or_ge w 0 with h' | h'
        · exact Or.inr (nw h')
        · left; clear * - cw h'; omega)
  push_cast at bx bh bk bv bw
  simp only [div_eq_mul_inv] at hE₁ hE₂ hP
  have nh : h ≠ -12 := by
    rintro rfl
    push_cast at hE₂ hP
    have hvinv : (v : ℚ)⁻¹ < 0 := by linarith [bx.2, bk.1]
    have hlow : (39 / 1666 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [bx.2, bw.2]
    obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
    have hzlt' : z₁ < 43 := by
      have : (z₁ : ℚ) < 43 := by norm_num at hzlt; linarith
      exact_mod_cast this
    have hz : z₁ = 39 := by clear * - hzpos hzlt' cz; omega
    subst hz
    push_cast at hP
    have hv : v < 0 := by
      have : (v : ℚ) < 0 := inv_lt_zero.mp hvinv
      exact_mod_cast this
    have hwneg : w < 0 := by have := nv hv; omega
    linarith [bx.2, inv_cast_neg hwneg]
  have nx : x ≠ -13 := by
    rintro rfl
    push_cast at hE₂
    have hup : (v : ℚ)⁻¹ < -(1 / 87) := by linarith [bh.2, bk.1]
    obtain ⟨hneg, hgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hgt' : -87 < v := by
      have : (-87 : ℚ) < v := by norm_num at hgt; linarith
      exact_mod_cast this
    have := nv hneg
    omega
  have bx' := inv_mem_of_le_or_le (A := 51) (B := 77) (by norm_num) (by norm_num) (x := x)
    (by clear * - cx nx; omega)
  have bh' := inv_mem_of_le_or_le (A := 52) (B := 76) (by norm_num) (by norm_num) (x := h)
    (by clear * - ch nh; omega)
  push_cast at bx' bh'
  have hlow : (1 / 295 : ℚ) < (z₁ : ℚ)⁻¹ := by linarith [bx.2, bh'.1, bk.1, bw.1]
  obtain ⟨hzpos, hzlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow
  have hzlt' : z₁ < 295 := by
    have : (z₁ : ℚ) < 295 := by norm_num at hzlt; exact hzlt
    exact_mod_cast this
  have hz : z₁ = 39 ∨ z₁ = 103 ∨ z₁ = 167 ∨ z₁ = 231 := by clear * - hzpos hzlt' cz; omega
  rcases hz with hz | hz | hz | hz <;> subst hz <;> push_cast at hE₁ hE₂
  ·
    have hlow' : (1 / 108 : ℚ) < (w : ℚ)⁻¹ := by linarith [bx'.1, bh.2, bk.2]
    obtain ⟨hwpos, hwlt⟩ := pos_lt_of_lt_inv (by norm_num) hlow'
    have hwlt' : w < 108 := by
      have : (w : ℚ) < 108 := by norm_num at hwlt; exact hwlt
      exact_mod_cast this
    have hw : w = 54 := by clear * - hwpos hwlt' cw; omega
    have hv : v = -23 := by omega
    have := nv (by omega)
    omega
  ·
    obtain ⟨p₁, p₂, p₃, -⟩ := hp 103 (by norm_num) (Or.inl (by decide))
    push_cast at p₁ p₂ p₃
    exact lyons_T_103 x h k v w cx ch ck cw (by linarith) (by linarith) (by linarith) hE₁ hE₂ hL
  ·
    obtain ⟨p₁, p₂, p₃, p₄⟩ := hp 167 (by norm_num) (Or.inl (by decide))
    push_cast at p₁ p₂ p₃ p₄
    have key : ∀ y : ℤ, (167 : ℤ) ≤ |y| + 1 →
        -(1 / 166 : ℚ) ≤ (y : ℚ)⁻¹ ∧ (y : ℚ)⁻¹ ≤ 1 / 166 := fun y hy => by
      have := inv_mem_of_le_or_le (A := 166) (B := 166) (by norm_num) (by norm_num) (x := y)
        (by rcases le_abs'.mp (by linarith : (166 : ℤ) ≤ |y|) with h' | h' <;> omega)
      push_cast at this
      exact this
    linarith [(key x p₁).2, (key h p₂).1, (key k p₃).1, (key w p₄).1]
  ·
    have hup : (w : ℚ)⁻¹ < -(1 / 162) := by linarith [bx.2, bh'.1, bk.1]
    obtain ⟨hwneg, hwgt⟩ := neg_gt_of_inv_lt (by norm_num) hup
    have hwgt' : -162 < w := by
      have : (-162 : ℚ) < w := by norm_num at hwgt; linarith
      exact_mod_cast this
    have hw : w = -138 := by have := nw hwneg; clear * - this hwgt' cw; omega
    have hv : v = -599 := by omega
    have := (hp 599 (by norm_num) (Or.inr (by rw [hv]; decide))).2.2.2
    rw [hw] at this
    norm_num at this

end CFSG.LyonsUnitaryFour
