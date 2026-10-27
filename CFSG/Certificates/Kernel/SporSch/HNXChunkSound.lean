module

public import Certificates.Data.Kernel.SporSch.HNXChunk
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
import CFSG.Certificates.Kernel.SporSch.HNXCnt.Lanes
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] def packW (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => x + 2 ^ w * packW w l

theorem fld_packW {w : Nat} : ∀ {l : List Nat}, (∀ x ∈ l, x < 2 ^ w) → ∀ {k : Nat}, k < l.length →
    fldW (packW w l) (w * k) w = l[k]!
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: l, hl, k, hk => by
    have hx := hl x List.mem_cons_self
    rw [fldW_eq, packW]
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      rfl
    · rw [show w * (k + 1) = w + w * k by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add,
        ← fldW_eq, fld_packW (fun y hy => hl y (List.mem_cons_of_mem _ hy))
          (by simp only [List.length_cons] at hk; omega)]
      rfl

theorem fld_sliceP (P m : Nat) {k : Nat} (hk : k < 64) :
    fldW (sliceP P m) (21 * k) 21 = fldW P (21 * (64 * m + k)) 21 := by
  change fldW (fldW P (1344 * m) 1344) (21 * k) 21 = _
  rw [fldW_eq, fldW_eq, fldW_eq, lanes_dm _ _ _ _ (by omega), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
  congr 3
  ring

theorem fldW_lt_two_pow (r o w : Nat) : fldW r o w < 2 ^ w := by
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem fld_or_low {a v s o : Nat} (ho : o + 21 ≤ s) :
    fldW (a ||| (v <<< s)) o 21 = fldW a o 21 := by
  rw [fldW_eq, fldW_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_lor,
    Nat.testBit_shiftLeft]
  by_cases hi : i < 21
  · have : ¬ (i + o ≥ s) := by omega
    simp [hi, this]
  · simp [hi]

theorem fld_or_top {a v s : Nat} (ha : a < 2 ^ s) (hv : v < 2 ^ 21) :
    fldW (a ||| (v <<< s)) s 21 = v := by
  rw [fldW_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_lor,
    Nat.testBit_shiftLeft]
  have h1 : a.testBit (i + s) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h2 : i + s ≥ s := by omega
  by_cases hi : i < 21
  · simp [hi, h1, h2]
  · have h3 : v.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, h3]

theorem or_shift_lt {a v s : Nat} (ha : a < 2 ^ s) (hv : v < 2 ^ 21) :
    a ||| (v <<< s) < 2 ^ (s + 21) := by
  apply Nat.or_lt_two_pow
  · exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
  · rw [Nat.shiftLeft_eq, Nat.pow_add, mul_comm]
    exact Nat.mul_lt_mul_of_pos_left hv (Nat.two_pow_pos s)

theorem fld_imgP (P S m : Nat) : ∀ c, imgP P S m c < 2 ^ (21 * c) ∧ ∀ k < c,
    fldW (imgP P S m c) (21 * k) 21 = fldW P (21 * fldW S (14 * (64 * m + k)) 14) 21
  | 0 => ⟨by unfold imgP; exact Nat.two_pow_pos _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | c + 1 => by
    obtain ⟨hlt, hf⟩ := fld_imgP P S m c
    have e : imgP P S m (c + 1) = imgP P S m c |||
        (fldW P (21 * fldW S (14 * (64 * m + c)) 14) 21 <<< (21 * c)) := rfl
    rw [e]
    refine ⟨by
      rw [show 21 * (c + 1) = 21 * c + 21 by ring]
      exact or_shift_lt hlt (fldW_lt_two_pow _ _ _),
      fun k hk => ?_⟩
    rcases Nat.lt_or_ge k c with h | h
    · rw [fld_or_low (by omega), hf k h]
    · obtain rfl : k = c := by omega
      exact fld_or_top hlt (fldW_lt_two_pow _ _ _)

theorem chunk_pos {N nc p : Nat} (hN : N ≤ 64 * nc) (hp : p < N) :
    p / 64 < nc ∧ p % 64 < cntP N (p / 64) ∧ cntP N (p / 64) ≤ 64 ∧
      64 * (p / 64) + p % 64 = p := by
  unfold cntP
  change p / 64 < nc ∧ p % 64 < min 64 (N - 64 * (p / 64)) ∧ min 64 (N - 64 * (p / 64)) ≤ 64 ∧ _
  refine ⟨by omega, ?_, Nat.min_le_left _ _, Nat.div_add_mod p 64⟩
  rw [Nat.lt_min]
  omega

end CFSG.KS.SporSch.HNXP

end
