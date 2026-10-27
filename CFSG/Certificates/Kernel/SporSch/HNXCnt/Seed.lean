module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Char
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch

@[expose] def seed_lane (x k : Nat) : Nat := x / 2 ^ (13 * k) % 2 ^ 13

@[expose] def seed_E (cs : List Char) : List Nat :=
  (cs.filter fun c => !CFSG.Sporadic.He.Native.wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

theorem seed_bIf (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem seed_bAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> cases b <;> rfl

theorem seed_lane_zero (k : Nat) : seed_lane 0 k = 0 := by
  simp [seed_lane]

theorem seed_testBit (X b w r : Nat) :
    (X / 2 ^ b % 2 ^ w).testBit r = (decide (r < w) && X.testBit (r + b)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem seed_lane_or_shl {a v j k : Nat} (hv : v < 2 ^ 13) :
    seed_lane (a ||| v <<< (13 * j)) k = if k = j then seed_lane a k ||| v else seed_lane a k := by
  unfold seed_lane
  apply Nat.eq_of_testBit_eq
  intro r
  rw [seed_testBit, Nat.testBit_lor, Nat.testBit_shiftLeft]
  by_cases hkj : k = j
  · subst hkj
    rw [if_pos rfl, Nat.testBit_lor, seed_testBit]
    by_cases hr : r < 13
    · simp [hr]
    · have hv' : v.testBit r = false := Nat.testBit_eq_false_of_lt
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hr, hv']
  · rw [if_neg hkj, seed_testBit]
    by_cases hr : r < 13
    · have hz : (decide (r + 13 * k ≥ 13 * j) && v.testBit (r + 13 * k - 13 * j)) = false := by
        by_cases hge : r + 13 * k ≥ 13 * j
        · have hlt : 13 ≤ r + 13 * k - 13 * j := by omega
          have hv' := Nat.testBit_eq_false_of_lt
            (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hlt))
          simp [hv']
        · simp [hge]
      rw [hz, Bool.or_false]
    · simp [hr]

theorem seed_ent13_eq (W r c : Nat) (hc : c < 133) :
    ent13 W r c = seed_lane (fldW W (1729 * r) 1729) c := by
  rw [fldW_eq]
  unfold ent13 seed_lane
  apply Nat.eq_of_testBit_eq
  intro t
  rw [seed_testBit, seed_testBit, seed_testBit]
  by_cases ht : t < 13
  · have h2 : t + 13 * c < 1729 := by omega
    simp only [ht, h2, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [ht]

theorem seed_char_eq (c : Char) (n : Nat) (d : Char) (hd : d.toNat = n) :
    (c == d) = (c.toNat == n) := by
  rw [← hd]
  by_cases h : c = d
  · subst h; simp
  · have h' : c.toNat ≠ d.toNat := fun e => h (Char.toNat_inj.1 e)
    simp [h, h']

theorem seed_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem seed_ble_false {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases e : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true e) h

theorem seed_ws (c : Char) : wsKX c.toNat = CFSG.Sporadic.He.Native.wsChar c := by
  unfold wsKX CFSG.Sporadic.He.Native.wsChar
  rw [seed_char_eq c 32 ' ' rfl, seed_char_eq c 9 '\t' rfl, seed_char_eq c 10 '\n' rfl,
    seed_char_eq c 13 '\r' rfl, seed_bIf, seed_bAnd]
  generalize c.toNat = n
  apply Bool.eq_iff_iff.2
  by_cases h32 : n = 32
  · subst h32; decide
  · rw [seed_beq_false h32, if_neg (by simp)]
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, beq_iff_eq]
    omega

theorem seed_dig (c : Char) :
    dig5KX c.toNat = (if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0) % 5 := by
  have h1 : ('0' ≤ c) ↔ 48 ≤ c.toNat := by
    change ('0' : Char).val ≤ c.val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have h2 : (c ≤ '9') ↔ c.toNat ≤ 57 := by
    change c.val ≤ ('9' : Char).val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have e0 : ('0' : Char).toNat = 48 := rfl
  unfold dig5KX
  rw [e0]
  by_cases a : 48 ≤ c.toNat <;> by_cases b : c.toNat ≤ 57
  · have hb : (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) = true := by simp [a, b]
    rw [← seed_bAnd] at hb
    rw [hb]
    simp [h1.2 a, h2.2 b]
    rfl
  all_goals
    have hb : (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) = false := by
      first
        | rw [seed_ble_false a, Bool.false_and]
        | rw [seed_ble_false b, Bool.and_false]
    rw [← seed_bAnd] at hb
    rw [hb]
    simp [h1, h2, a, b]

theorem seed_cons0 (W : Nat) (ch : Char) (cs : List Char) (i j acc : Nat) :
    seedRun W (ch :: cs) 0 i j acc =
      if ch.toNat = 10 then seedRun W cs 1 i j acc else seedRun W cs 0 i j acc := by
  have e : seedRun W (ch :: cs) 0 i j acc = strictB ch.toNat (fun c =>
      bIf(Nat.beq c 10, seedRun W cs 1 i j acc, seedRun W cs 0 i j acc)) := rfl
  rw [e, strictB_eq, seed_bIf]
  simp only [Nat.beq_eq]

theorem seed_cons1 (W : Nat) (ch : Char) (cs : List Char) (i j acc : Nat) :
    seedRun W (ch :: cs) 1 i j acc =
      if wsKX ch.toNat = true then seedRun W cs 1 i j acc
      else if i = 133 then seedRun W cs 1 i j acc
      else if j = 132 then
        (if fldW W (1729 * i) 1729 = (acc ||| dig5KX ch.toNat <<< (13 * j)) then
          seedRun W cs 1 (i + 1) 0 0 else false)
      else seedRun W cs 1 i (j + 1) (acc ||| dig5KX ch.toNat <<< (13 * j)) := by
  have e : seedRun W (ch :: cs) 1 i j acc = strictB ch.toNat (fun c =>
      bIf(wsKX c, seedRun W cs 1 i j acc,
      bIf(Nat.beq i 133, seedRun W cs 1 i j acc,
        strictB (Nat.lor acc (Nat.shiftLeft (dig5KX c) (Nat.mul (nat_lit 13) j))) (fun a =>
          bIf(Nat.beq j 132,
            bAnd(Nat.beq (fldW W (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) a,
              strictB (Nat.succ i) (fun i' => seedRun W cs 1 i' 0 0)),
            strictB (Nat.succ j) (fun j' => seedRun W cs 1 i j' a)))))) := rfl
  rw [e]
  simp only [strictB_eq, seed_bIf, seed_bAnd, Nat.beq_eq, Nat.succ_eq_add_one]
  rfl

theorem seed_ph0 (W : Nat) : ∀ (cs : List Char) (i j acc : Nat),
    seedRun W cs 0 i j acc = true →
      seedRun W ((cs.dropWhile (· != '\n')).drop 1) 1 i j acc = true := by
  intro cs
  induction cs with
  | nil =>
    intro i j acc h
    rw [show seedRun W [] 0 i j acc = false from rfl] at h
    exact absurd h Bool.false_ne_true
  | cons ch cs ih =>
    intro i j acc h
    rw [seed_cons0] at h
    by_cases hc : ch = '\n'
    · subst hc
      have h10 : ('\n' : Char).toNat = 10 := rfl
      rw [if_pos h10] at h
      rw [List.dropWhile_cons_of_neg (by simp)]
      exact h
    · have h' : ch.toNat ≠ 10 := fun e => hc (Char.toNat_inj.1 e)
      rw [if_neg h'] at h
      rw [List.dropWhile_cons_of_pos (by simpa using hc)]
      exact ih i j acc h

theorem seed_E_ws {ch : Char} (cs : List Char) (hw : CFSG.Sporadic.He.Native.wsChar ch = true) :
    seed_E (ch :: cs) = seed_E cs := by
  unfold seed_E
  rw [List.filter_cons_of_neg (by simp [hw])]

theorem seed_E_cons {ch : Char} (cs : List Char)
    (hw : ¬ CFSG.Sporadic.He.Native.wsChar ch = true) :
    seed_E (ch :: cs) = (if '0' ≤ ch && ch ≤ '9' then ch.toNat - '0'.toNat else 0) :: seed_E cs := by
  unfold seed_E
  rw [List.filter_cons_of_pos (by simpa using hw), List.map_cons]

theorem seed_run1 {W : Nat} : ∀ (cs : List Char) (i j acc : Nat),
    seedRun W cs 1 i j acc = true → i < 133 → j < 133 →
    (∀ c, j ≤ c → seed_lane acc c = 0) →
    ∀ r, i ≤ r → r < 133 → ∀ c < 133, ent13 W r c =
      if r = i ∧ c < j then seed_lane acc c
      else (seed_E cs).getD (133 * r + c - (133 * i + j)) 0 % 5 := by
  intro cs
  induction cs with
  | nil =>
    intro i j acc h hi
    have e : seedRun W [] 1 i j acc = (Nat.beq 1 1 && Nat.beq i 133) := by
      rw [← seed_bAnd]; rfl
    rw [e, seed_beq_false (by omega : i ≠ 133), Bool.and_false] at h
    exact absurd h Bool.false_ne_true
  | cons ch cs ih =>
    intro i j acc h hi hj hacc r hir hr c hc
    rw [seed_cons1] at h
    by_cases hw : wsKX ch.toNat = true
    · rw [if_pos hw] at h
      rw [seed_E_ws cs (by rw [← seed_ws]; exact hw)]
      exact ih i j acc h hi hj hacc r hir hr c hc
    · rw [if_neg hw, if_neg (by omega : i ≠ 133)] at h
      rw [seed_E_cons cs (by rw [← seed_ws]; exact hw)]
      have hd := seed_dig ch
      generalize (if '0' ≤ ch && ch ≤ '9' then ch.toNat - '0'.toNat else 0) = d at hd ⊢
      have hv5 : dig5KX ch.toNat < 5 := by rw [seed_dig]; exact Nat.mod_lt _ (by norm_num)
      have hv : dig5KX ch.toNat < 2 ^ 13 := Nat.lt_trans hv5 (by norm_num)
      have hacc' : ∀ c', seed_lane (acc ||| dig5KX ch.toNat <<< (13 * j)) c' =
          if c' = j then dig5KX ch.toNat else seed_lane acc c' := by
        intro c'
        rw [seed_lane_or_shl hv]
        split_ifs with h'
        · rw [h', hacc j le_rfl, Nat.zero_or]
        · rfl
      by_cases hj1 : j = 132
      · rw [if_pos hj1] at h
        by_cases h1 : fldW W (1729 * i) 1729 = (acc ||| dig5KX ch.toNat <<< (13 * j))
        swap
        · rw [if_neg h1] at h
          exact absurd h Bool.false_ne_true
        rw [if_pos h1] at h
        rcases Nat.eq_or_lt_of_le hir with rfl | hlt
        · rw [seed_ent13_eq W _ c hc, h1, hacc' c]
          split_ifs with hcj hcj'
          · omega
          · subst hcj
            rw [Nat.sub_self, List.getD_cons_zero, hd]
          · rfl
          · omega
        · have := ih (i + 1) 0 0 h (by omega) (by omega) (fun c _ => seed_lane_zero c) r hlt hr c hc
          rw [this, if_neg (by omega), if_neg (by omega)]
          have e2 : 133 * r + c - (133 * i + j) = (133 * r + c - (133 * (i + 1) + 0)) + 1 := by
            omega
          rw [e2, List.getD_cons_succ]
      · rw [if_neg hj1] at h
        have := ih i (j + 1) _ h hi (by omega) (fun c' h1 => by
          rw [hacc' c', if_neg (by omega)]
          exact hacc c' (by omega)) r hir hr c hc
        rw [this, hacc' c]
        by_cases hri : r = i
        · subst hri
          by_cases hcj : c < j
          · rw [if_pos (And.intro rfl (by omega)), if_pos (And.intro rfl hcj), if_neg (by omega)]
          · by_cases hcj' : c = j
            · subst hcj'
              rw [if_pos (And.intro rfl (by omega)), if_pos rfl, if_neg (by omega), Nat.sub_self,
                List.getD_cons_zero, hd]
            · rw [if_neg (by omega), if_neg (by omega)]
              have e2 : 133 * r + c - (133 * r + j) = (133 * r + c - (133 * r + (j + 1))) + 1 := by
                omega
              rw [e2, List.getD_cons_succ]
        · rw [if_neg (by omega), if_neg (by omega)]
          have e2 : 133 * r + c - (133 * i + j) = (133 * r + c - (133 * i + (j + 1))) + 1 := by
            omega
          rw [e2, List.getD_cons_succ]

theorem seed_get_ofFn {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem seedRK_rows {W : Nat} {cs : List Char} (h : seedRK W cs = true) :
    ∀ i < 133, ∀ j < 133,
      ((CFSG.Sporadic.He.Native.rowsOf 5 133 (String.ofList cs))[i]!)[j]! = ent13 W i j := by
  intro i hi j hj
  unfold seedRK at h
  have hrun := seed_run1 _ 0 0 0 (seed_ph0 W cs 0 0 0 h) (by norm_num) (by norm_num)
    (fun c _ => seed_lane_zero c) i (Nat.zero_le _) hi j hj
  rw [if_neg (by omega), Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hrun
  have hdec : CFSG.Sporadic.He.Native.decodeEntries (String.ofList cs) =
      seed_E ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold CFSG.Sporadic.He.Native.decodeEntries
    rw [String.toList_ofList]
    rfl
  unfold CFSG.Sporadic.He.Native.rowsOf
  rw [hdec, seed_get_ofFn _ hi, seed_get_ofFn _ hj, hrun, List.getElem?_toArray,
    List.getD_eq_getElem?_getD, Nat.mul_comm i 133]

end CFSG.KS.SporSch.HNXP

end
