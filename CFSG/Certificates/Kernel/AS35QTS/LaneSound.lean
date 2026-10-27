module

public import Certificates.Data.Kernel.AS35QTS.Planes
public import CFSG.Certificates.Kernel.AS35QTS.CircuitSound
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd)

theorem blk_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    blk w f (n + 1) = 2 ^ (w * n) * f n + blk w f n := by
  change blk w f n + f n <<< (w * n) = _
  rw [Nat.shiftLeft_eq]
  ring

theorem blk_lt {w : Nat} {f : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i < 2 ^ w) →
    blk w f n < 2 ^ (w * n)
  | 0, _ => by change 0 < 2 ^ (w * 0); positivity
  | n + 1, hf => by
    rw [blk_succ]
    have h1 := blk_lt (n := n) fun i hi => hf i (by omega)
    have h2 := hf n (by omega)
    have e : 2 ^ (w * (n + 1)) = 2 ^ (w * n) * 2 ^ w := by rw [Nat.mul_succ, pow_add]
    rw [e]
    have : 2 ^ (w * n) * f n + 2 ^ (w * n) ≤ 2 ^ (w * n) * 2 ^ w := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ h2
    omega

theorem blk_testBit {w : Nat} {f : Nat → Nat} (hw : 0 < w) : ∀ {n : Nat}, (∀ i < n, f i < 2 ^ w) →
    ∀ c, (blk w f n).testBit c = (decide (c < w * n) && (f (c / w)).testBit (c % w))
  | 0, _, c => by
    change Nat.testBit 0 c = _
    simp
  | n + 1, hf, c => by
    have ih := blk_testBit hw (n := n) fun i hi => hf i (by omega)
    rw [blk_succ, Nat.testBit_two_pow_mul_add _ (blk_lt fun i hi => hf i (by omega))]
    by_cases hc : c < w * n
    · rw [if_pos hc, ih c]
      have : c < w * (n + 1) := by nlinarith
      simp [hc, this]
    · rw [if_neg hc]
      by_cases hc' : c < w * (n + 1)
      · have hq : c / w = n :=
          Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; exact hc')
        have hr : c % w = c - w * n := by
          have := Nat.div_add_mod c w
          rw [hq] at this
          omega
        simp [hc', hq, hr]
      · have hlt := hf n (by omega)
        have hbig : 2 ^ w ≤ 2 ^ (c - w * n) := Nat.pow_le_pow_right (by norm_num) (by
          rw [Nat.mul_succ] at hc'
          omega)
        simp only [hc', decide_false, Bool.false_and]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hbig)

theorem bitN_lt (g b : Nat) : bitN g b < 2 := by
  change (g >>> b) &&& 1 < 2
  rw [Nat.and_one_is_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem bitN_testBit (g b : Nat) : (bitN g b).testBit 0 = g.testBit b := by
  change ((g >>> b) &&& 1).testBit 0 = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  simp

theorem colB_testBit (b : Nat) : ∀ (G : List Nat) (k : Nat),
    (colB b G).testBit k = (G.getD k 0).testBit b
  | [], k => by
    change Nat.testBit 0 k = _
    simp
  | g :: G, k => by
    change (Nat.add (bitN g b) (Nat.mul 2 (colB b G))).testBit k = _
    have h2 := bitN_lt g b
    cases k with
    | zero =>
      change (bitN g b + 2 * colB b G).testBit 0 = _
      rw [List.getD_cons_zero, ← bitN_testBit g b, Nat.testBit_zero, Nat.testBit_zero]
      congr 1
      apply propext
      omega
    | succ k =>
      rw [List.getD_cons_succ, ← colB_testBit b G k, Nat.testBit_succ]
      congr 1
      change (bitN g b + 2 * colB b G) / 2 = _
      omega

theorem colB_lt (b : Nat) : ∀ G : List Nat, colB b G < 2 ^ G.length
  | [] => by change 0 < 1; norm_num
  | g :: G => by
    change Nat.add (bitN g b) (Nat.mul 2 (colB b G)) < 2 ^ (G.length + 1)
    have := colB_lt b G
    have := bitN_lt g b
    rw [pow_succ]
    change bitN g b + 2 * colB b G < _
    omega

theorem blkMask_testBit {w : Nat} (hw : 0 < w) (s n c : Nat) :
    (blk w (fun i => Nat.mul (bitN i s) (Nat.sub (Nat.pow 2 w) 1)) n).testBit c =
      (decide (c < w * n) && (c / w).testBit s) := by
  have hf : ∀ i < n, Nat.mul (bitN i s) (Nat.sub (Nat.pow 2 w) 1) < 2 ^ w := by
    intro i _
    have h1 : bitN i s ≤ 1 := by have := bitN_lt i s; omega
    change bitN i s * (2 ^ w - 1) < 2 ^ w
    calc bitN i s * (2 ^ w - 1) ≤ 1 * (2 ^ w - 1) := Nat.mul_le_mul_right _ h1
      _ < 2 ^ w := by rw [one_mul]; exact Nat.sub_lt (Nat.two_pow_pos _) one_pos
  rw [blk_testBit hw hf c]
  congr 1
  change (bitN (c / w) s * (2 ^ w - 1)).testBit (c % w) = _
  have hm : c % w < w := Nat.mod_lt _ hw
  rw [← bitN_testBit (c / w) s]
  have := bitN_lt (c / w) s
  interval_cases h : bitN (c / w) s
  · simp
  · rw [one_mul, Nat.testBit_two_pow_sub_one]
    simp [hm]

set_option exponentiation.threshold 700 in
theorem lanePl_testBit {G : List Nat} (hG : G.length = 648) (b c : Nat) (hc : c < 82944) :
    (lanePl G b).testBit c =
      if b < 18 then (G.getD (c % 648) 0).testBit b else (c / 648).testBit (b - 18) := by
  have hc' : c < 648 * 128 := by omega
  unfold lanePl
  by_cases hb : b < 18
  · have hbt : Nat.blt b 18 = true := Nat.blt_eq.mpr hb
    rw [hbt, if_pos hb]
    change (blk 648 (fun _ => colB b G) 128).testBit c = _
    rw [blk_testBit (by norm_num) (fun _ _ => by rw [← hG]; exact colB_lt b G) c,
      colB_testBit]
    simp [hc']
  · have hbt : Nat.blt b 18 = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hb (Nat.blt_eq.mp h)
    rw [hbt, if_neg hb]
    change (blk 648 (fun i => Nat.mul (bitN i (Nat.sub b 18)) (Nat.sub (Nat.pow 2 648) 1))
      128).testBit c = _
    rw [blkMask_testBit (by norm_num)]
    simp only [hc', decide_true, Bool.true_and]
    rfl

theorem frc_eqL (y : Nat) (k : Nat → Bool) : frc y k = k y := by
  cases y <;> rfl

theorem lanesK_eq (G : List Nat) (k : PL Nat → Bool) : lanesK G k = k (ofIx (lanePl G)) := by
  simp only [lanesK, frc_eqL]
  rfl

@[expose] def e4 (n : Nat) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def decN (n : Nat) : Cd :=
  ⟨if n.testBit 24 then 1 else 0, ⟨e4 (n >>> 22), e4 (n >>> 20), e4 (n >>> 18)⟩,
    ⟨⟨e4 (n >>> 16), e4 (n >>> 14), e4 (n >>> 12)⟩, ⟨e4 (n >>> 10), e4 (n >>> 8), e4 (n >>> 6)⟩,
      ⟨e4 (n >>> 4), e4 (n >>> 2), e4 n⟩⟩⟩

theorem lb_e4 (n s : Nat) : lb (e4 (n >>> s)) = n.testBit s := by
  change ((n >>> s) % 4).testBit 0 = _
  rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp

theorem hb_e4 (n s : Nat) : hb (e4 (n >>> s)) = n.testBit (s + 1) := by
  change ((n >>> s) % 4).testBit 1 = _
  rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [Nat.add_comm]

theorem eb_bit (n : Nat) : eb (if n.testBit 24 then 1 else 0) = n.testBit 24 := by
  cases n.testBit 24 <;> rfl

theorem ofCd_decN (n : Nat) : ofCd (decN n) = ofIx fun b => n.testBit b := by
  have h0l : lb (e4 n) = n.testBit 0 := by simpa using lb_e4 n 0
  have h0h : hb (e4 n) = n.testBit 1 := by simpa using hb_e4 n 0
  simp only [ofCd, decN, ofV, ofIx, lb_e4, hb_e4, eb_bit, h0l, h0h]

theorem lane_lanes {G : List Nat} (hG : G.length = 648) (hGb : ∀ g ∈ G, g < 2 ^ 18) {c : Nat}
    (hc : c < 82944) :
    laneOf c (ofIx (lanePl G)) = ofCd (decN (2 ^ 18 * (c / 648) + G.getD (c % 648) 0)) := by
  have hg : G.getD (c % 648) 0 < 2 ^ 18 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : G[c % 648]? with
    | none => simp
    | some g => exact hGb g (List.mem_of_getElem? h)
  have hb : ∀ b, (lanePl G b).testBit c = (2 ^ 18 * (c / 648) + G.getD (c % 648) 0).testBit b :=
    fun b => by rw [lanePl_testBit hG b c hc, Nat.testBit_two_pow_mul_add _ hg]
  rw [ofCd_decN]
  simp only [laneOf, mapP, ofIx, hb]

end CFSG.KC.AS35QTS

end
