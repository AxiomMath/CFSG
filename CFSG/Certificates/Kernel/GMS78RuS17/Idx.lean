module

public import Certificates.Data.Kernel.GMS78RuSClo
import CFSG.Certificates.Kernel.GMS78RuP.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

private theorem testBit_fget (X i w j : Nat) :
    (fget X i w).testBit j = (decide (j < w) && X.testBit (i * w + j)) := by
  have h1 : maskN w = 2 ^ w - 1 := by simp [maskN, pw2, Nat.shiftLeft_eq]
  change ((X >>> (i * w)) &&& maskN w).testBit j = _
  rw [h1, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

private theorem testBit_lt9 {v b : Nat} (hv : v < 512) (hb : 9 ≤ b) : v.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
    (Nat.le_trans (by decide : 512 ≤ 2 ^ 9) (Nat.pow_le_pow_right (by decide) hb)))

private theorem fget_lor_shl {X v a : Nat} (hv : v < 512) (hX : fget X a 9 = 0) (j : Nat) :
    fget (X ||| v <<< (9 * a)) j 9 = if j = a then v else fget X j 9 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fget, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hb : b < 9
  · by_cases hj : j = a
    · subst hj
      rw [if_pos rfl]
      have h1 : X.testBit (j * 9 + b) = false := by
        have := congrArg (fun x => x.testBit b) hX
        simp only [testBit_fget, Nat.zero_testBit] at this
        simpa [hb] using this
      rw [h1, show j * 9 + b - 9 * j = b by omega]
      simp [hb, show 9 * j ≤ j * 9 + b by omega]
    · rw [if_neg hj, testBit_fget]
      have : (decide (j * 9 + b ≥ 9 * a) && v.testBit (j * 9 + b - 9 * a)) = false := by
        rcases Nat.lt_or_gt_of_ne hj with h | h
        · have : ¬ j * 9 + b ≥ 9 * a := by omega
          simp [this]
        · rw [testBit_lt9 hv (by omega)]
          simp
      rw [this, Bool.or_false]
  · have hb' : decide (b < 9) = false := by simp [hb]
    rw [hb', Bool.false_and]
    split
    · exact (testBit_lt9 hv (by omega)).symm
    · rw [testBit_fget, hb', Bool.false_and]

private def idxRec (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) l

private theorem idxRec_fget : ∀ (l : List Nat) (i : Nat), l.Nodup → i + l.length < 512 →
    ∀ y, fget (idxRec l i) y 9 = if y ∈ l then i + 1 + l.idxOf y else 0
  | [], i, _, _, y => by
    have : idxRec [] i = 0 := rfl
    rw [this, fget_eq']
    simp
  | x :: l, i, hnd, hlen, y => by
    have e : idxRec (x :: l) i = (idxRec l (i + 1)) ||| (i + 1) <<< (9 * x) := by
      change Nat.lor _ _ = _
      rw [Nat.or_comm]
      rfl
    have hnd' := List.nodup_cons.1 hnd
    have hlen' : i + 1 + l.length < 512 := by simp at hlen; omega
    have hx : fget (idxRec l (i + 1)) x 9 = 0 := by
      rw [idxRec_fget l (i + 1) hnd'.2 hlen', if_neg hnd'.1]
    rw [e, fget_lor_shl (by simp at hlen; omega) hx, idxRec_fget l (i + 1) hnd'.2 hlen']
    by_cases h : y = x
    · subst h
      simp
    · by_cases hy : y ∈ l
      · simp [h, hy, List.idxOf_cons, Ne.symm h]
        omega
      · simp [h, hy]

theorem sIdx_fget {C : List Nat} (hnd : C.Nodup) (hlen : C.length < 512) (y : Nat) :
    fget (sIdx C) y 9 = if y ∈ C then C.idxOf y + 1 else 0 := by
  have e : sIdx C = idxRec C 0 := rfl
  rw [e, idxRec_fget C 0 hnd (by omega) y]
  simp [Nat.add_comm]

theorem sClosed_mem {m : Nat → Nat → Nat} {C : List Nat} (hnd : C.Nodup) (hlen : C.length < 512)
    (h : sClosed m C = true) : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C := by
  unfold sClosed at h
  rw [neStrictB_eq, neAllL_iff] at h
  intro p hp q hq
  have h1 := h p hp
  rw [neAllL_iff] at h1
  have h2 := h1 q hq
  rw [P117.notB_iff, Bool.eq_false_iff] at h2
  by_contra hn
  apply h2
  rw [P117.beq_eq, sIdx_fget hnd hlen, if_neg hn]
  rfl

private def pv8 : List Nat → Nat
  | [] => 0
  | x :: l => x + 256 * pv8 l

private theorem czPack8_aux : ∀ l : List Nat, (∀ x ∈ l, x < 256) → ∀ s,
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 8))) l s = pv8 l <<< s
  | [], _, s => by
    change 0 = 0 <<< s
    rw [Nat.zero_shiftLeft]
  | x :: l, hl, s => by
    change Nat.lor (Nat.shiftLeft x s) (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 8))) l (Nat.add s 8)) = _
    rw [czPack8_aux l (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
    have hx : x < 2 ^ 8 := hl x List.mem_cons_self
    change x <<< s ||| pv8 l <<< (s + 8) = (x + 256 * pv8 l) <<< s
    rw [Nat.add_comm s 8, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt hx]
    congr 1
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from rfl]
    omega

private theorem pv8_field : ∀ l : List Nat, (∀ x ∈ l, x < 256) → ∀ i,
    pv8 l / 2 ^ (i * 8) % 2 ^ 8 = l.getD i 0
  | [], _, i => by simp [pv8]
  | x :: l, hl, 0 => by
    have hx := hl x List.mem_cons_self
    simp only [pv8, Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [show (2 : Nat) ^ 8 = 256 from rfl]
    omega
  | x :: l, hl, i + 1 => by
    have hx := hl x List.mem_cons_self
    rw [List.getD_cons_succ, ← pv8_field l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) i,
      show (i + 1) * 8 = 8 + i * 8 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 2
    simp only [pv8]
    rw [show (2 : Nat) ^ 8 = 256 from rfl]
    omega

theorem czPack8_fget {l : List Nat} (hl : ∀ x ∈ l, x < 256) (i : Nat) :
    fget (czPack8 l) i 8 = l.getD i 0 := by
  have e : czPack8 l = pv8 l := (czPack8_aux l hl 0).trans Nat.shiftLeft_zero
  rw [e, fget_eq', pv8_field l hl]

end CFSG.KC.GMS.S17

end
