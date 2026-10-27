module

public import Certificates.Data.RouteP.Bridge
public import Certificates.Data.Kernel.RouteP.TextLines
import CFSG.Certificates.Kernel.B32Sound

public section

namespace CFSG.KS.RouteP

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.KC.RouteP

abbrev NLA := Array (Array UInt32) × Array UInt32 × UInt32 × Bool × Bool × Bool

@[expose] def nlStepA (s : NLA) (c : UInt8) : NLA :=
  if s.snd.snd.snd.snd.fst = true then
    if (c == 10) = true then (s.fst, s.snd.fst, s.snd.snd.fst, s.snd.snd.snd.fst, false, true)
    else (s.fst, s.snd.fst, s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst,
      s.snd.snd.snd.snd.snd)
  else if (s.snd.snd.snd.snd.snd && c == 35) = true then
    (s.fst, s.snd.fst, s.snd.snd.fst, s.snd.snd.snd.fst, true, s.snd.snd.snd.snd.snd)
  else if (decide (c ≥ 48) && decide (c ≤ 57)) = true then
    (s.fst, s.snd.fst, s.snd.snd.fst * 10 + (c - 48).toUInt32, true, s.snd.snd.snd.snd.fst, false)
  else if s.snd.snd.snd.fst = true then
    if (c == 10) = true then
      if (!(s.snd.fst.push s.snd.snd.fst).isEmpty) = true then
        (s.fst.push (s.snd.fst.push s.snd.snd.fst), #[], 0, false, s.snd.snd.snd.snd.fst, true)
      else (s.fst, s.snd.fst.push s.snd.snd.fst, 0, false, s.snd.snd.snd.snd.fst, true)
    else (s.fst, s.snd.fst.push s.snd.snd.fst, 0, false, s.snd.snd.snd.snd.fst, false)
  else if (c == 10) = true then
    if (!s.snd.fst.isEmpty) = true then
      (s.fst.push s.snd.fst, #[], s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst, true)
    else (s.fst, s.snd.fst, s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst, true)
  else (s.fst, s.snd.fst, s.snd.snd.fst, s.snd.snd.snd.fst, s.snd.snd.snd.snd.fst, false)

@[expose] def nlFinA (s : NLA) : Array (Array UInt32) :=
  if s.snd.snd.snd.fst = true then
    if (!(s.snd.fst.push s.snd.snd.fst).isEmpty) = true then
      s.fst.push (s.snd.fst.push s.snd.snd.fst)
    else s.fst
  else if (!s.snd.fst.isEmpty) = true then s.fst.push s.snd.fst else s.fst

theorem forIn_yield_foldl {α β : Type} (l : List α) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) (init : β) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h]
    exact ih _

theorem foldl_range'_get {β : Type} (g : β → UInt8 → β) :
    ∀ (l pre : List UInt8) (init : β),
      (List.range' pre.length l.length).foldl (fun b i => g b (pre ++ l)[i]!) init = l.foldl g init
  | [], _, _ => rfl
  | a :: l, pre, init => by
    rw [List.length_cons, List.range'_succ, List.foldl_cons, List.foldl_cons]
    have e : (pre ++ a :: l)[pre.length]! = a := by
      rw [getElem!_pos _ _ (by simp)]
      simp
    rw [e]
    have := foldl_range'_get g l (pre ++ [a]) (g init a)
    rw [List.length_append, List.length_singleton] at this
    rw [← this]
    congr 1
    funext b i
    rw [List.append_assoc]
    rfl

theorem numLines_eq_foldl (s : String) :
    numLines s = nlFinA (s.toUTF8.data.toList.foldl nlStepA (#[], #[], 0, false, false, true)) := by
  unfold numLines
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_yield_foldl _ _ (fun st i => nlStepA st (s.toUTF8.get! i))]
  · have hs : [:s.toUTF8.size].size = s.toUTF8.data.toList.length := by
      rw [Std.Legacy.Range.size, Array.length_toList]
      change (s.toUTF8.size - 0 + 1 - 1) / 1 = s.toUTF8.size
      omega
    rw [hs]
    have := foldl_range'_get nlStepA s.toUTF8.data.toList [] (#[], #[], 0, false, false, true)
    rw [List.length_nil, List.nil_append] at this
    have hget : ∀ (b : ByteArray) (i : Nat), b.get! i = b.data.toList[i]! := by
      intro b i
      cases b with
      | mk bs =>
        change bs[i]! = bs.toList[i]!
        rw [getElem!_def, getElem!_def, Array.getElem?_toList]
    simp only [hget]
    rw [this]
    rfl
  · intro a b
    unfold nlStepA
    split_ifs <;> rfl

@[expose] def toArr (l : List Nat) : Array UInt32 := (l.reverse.map UInt32.ofNat).toArray

@[expose] def toA (s : NLL) : NLA :=
  ((s.1.reverse.map fun l => (l.map UInt32.ofNat).toArray).toArray, toArr s.2.1,
    UInt32.ofNat s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2)

theorem toArr_cons (a : Nat) (l : List Nat) : toArr (a :: l) = (toArr l).push (UInt32.ofNat a) := by
  simp [toArr]

theorem toArr_isEmpty (l : List Nat) : (toArr l).isEmpty = decide (l = []) := by
  cases l <;> simp [toArr]

theorem toArr_eq (l : List Nat) : toArr l = (l.reverse.map UInt32.ofNat).toArray := rfl

theorem u8_beq {n m : Nat} (hn : n < 256) (hm : m < 256) :
    (UInt8.ofNat n == UInt8.ofNat m) = decide (n = m) := by
  by_cases h : n = m
  · subst h
    simp
  · have : UInt8.ofNat n ≠ UInt8.ofNat m := by
      intro e
      have := congrArg UInt8.toNat e
      simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
      exact h this
    simp [h, this]

theorem u8_toNat {n : Nat} (hn : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem nlStepA_toA (s : NLL) {n : Nat} (hn : n < 128) :
    nlStepA (toA s) (UInt8.ofNat n) = toA (nlStepL s n) := by
  obtain ⟨out, cur, num, inNum, comment, atStart⟩ := s
  have h10 : (UInt8.ofNat n == 10) = decide (n = 10) := u8_beq (m := 10) (by omega) (by decide)
  have h35 : (UInt8.ofNat n == 35) = decide (n = 35) := u8_beq (m := 35) (by omega) (by decide)
  have hge : decide (UInt8.ofNat n ≥ 48) = decide (48 ≤ n) := by
    apply decide_eq_decide.mpr
    rw [ge_iff_le, UInt8.le_iff_toNat_le, u8_toNat (by omega)]
    rfl
  have hle : decide (UInt8.ofNat n ≤ 57) = decide (n ≤ 57) := by
    apply decide_eq_decide.mpr
    rw [UInt8.le_iff_toNat_le, u8_toNat (by omega)]
    rfl
  have hsub : 48 ≤ n → (UInt8.ofNat n - 48).toUInt32 = UInt32.ofNat (n - 48) := by
    intro h
    apply UInt32.toNat_inj.mp
    rw [UInt8.toNat_toUInt32, UInt8.toNat_sub_of_le _ _ (by
      rw [UInt8.le_iff_toNat_le, u8_toNat (by omega)]
      exact h), u8_toNat (by omega)]
    change n - 48 = (n - 48) % 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega)]
  unfold nlStepA nlStepL toA
  simp only [h10, h35, hge, hle, decide_eq_true_eq, Bool.and_eq_true]
  by_cases hc : comment = true
  · simp only [hc, if_true]
    by_cases hn10 : n = 10 <;> simp [hn10]
  · simp only [hc, Bool.false_eq_true, if_false]
    by_cases hs : atStart = true ∧ n = 35
    · simp only [hs, if_true, and_self]
    · simp only [hs, if_false]
      by_cases hd : 48 ≤ n ∧ n ≤ 57
      · simp only [hd, if_true, and_self]
        rw [hsub hd.1]
        simp [UInt32.ofNat_add, UInt32.ofNat_mul]
      · simp only [hd, if_false]
        by_cases hi : inNum = true
        · simp only [hi, if_true]
          by_cases hn10 : n = 10
          · simp [hn10, toArr_cons, toArr_isEmpty, toArr]
          · simp [hn10, toArr_cons]
        · simp only [hi, Bool.false_eq_true, if_false]
          by_cases hn10 : n = 10
          · by_cases hcur : cur = []
            · simp [hn10, hcur, toArr]
            · simp [hn10, hcur, toArr_isEmpty, toArr]
          · simp [hn10]

theorem nlFinA_toA (s : NLL) :
    nlFinA (toA s) = ((nlFinL s).map fun l => (l.map UInt32.ofNat).toArray).toArray := by
  obtain ⟨out, cur, num, inNum, comment, atStart⟩ := s
  unfold nlFinA nlFinL toA
  by_cases hi : inNum = true
  · simp [hi, toArr_cons, toArr]
  · by_cases hcur : cur = []
    · simp [hi, hcur, toArr]
    · simp [hi, hcur, toArr_isEmpty, toArr]

theorem foldl_toA : ∀ (ns : List Nat) (s : NLL), (∀ n ∈ ns, n < 128) →
    (ns.map UInt8.ofNat).foldl nlStepA (toA s) = toA (ns.foldl nlStepL s)
  | [], _, _ => rfl
  | n :: ns, s, h => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, nlStepA_toA s (h n (by simp))]
    exact foldl_toA ns _ fun m hm => h m (by simp [hm])

theorem forceN_eq {β : Type} (n : Nat) (k : Nat → β) : forceN n k = k n := by
  cases n <;> rfl

theorem bif'_eq (c t e : Bool) : bif' c t e = if c = true then t else e := by
  cases c <;> rfl

section Chk

variable (E : Nat → Nat → Nat) (lens : Nat → Nat)

@[expose] def rowL (i : Nat) : List Nat := (List.range (lens i)).map (E i)

@[expose] def stN (L P num iN cm sa : Nat) : NLL :=
  ((List.range L).reverse.map (rowL E lens), ((List.range P).map (E L)).reverse, num,
    iN == 1, cm == 1, sa == 1)

theorem nlChk_cons (n : Nat) (ns : List Nat) (L P num iN cm sa : Nat)
    (fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool) :
    nlChk E lens (n :: ns) L P num iN cm sa fin =
      bif' (Nat.blt n 128)
        (bif' (Nat.beq cm 1)
          (bif' (Nat.beq n 10) (nlChk E lens ns L P num iN 0 1 fin)
            (nlChk E lens ns L P num iN cm sa fin))
          (bif' (and (Nat.beq sa 1) (Nat.beq n 35)) (nlChk E lens ns L P num iN 1 sa fin)
            (bif' (and (Nat.ble 48 n) (Nat.ble n 57))
              (forceN (Nat.add (Nat.mul num 10) (Nat.sub n 48)) fun m =>
                nlChk E lens ns L P m 1 cm 0 fin)
              (bif' (Nat.beq iN 1)
                (bif' (Nat.beq (E L P) num)
                  (forceN (Nat.succ P) fun P' =>
                    bif' (Nat.beq n 10)
                      (bif' (Nat.beq P' (lens L))
                        (forceN (Nat.succ L) fun L' => nlChk E lens ns L' 0 0 0 cm 1 fin) false)
                      (nlChk E lens ns L P' 0 0 cm 0 fin))
                  false)
                (bif' (Nat.beq n 10)
                  (bif' (Nat.beq P 0) (nlChk E lens ns L 0 num 0 cm 1 fin)
                    (bif' (Nat.beq P (lens L))
                      (forceN (Nat.succ L) fun L' => nlChk E lens ns L' 0 num 0 cm 1 fin) false))
                  (nlChk E lens ns L P num 0 cm 0 fin))))))
        false := rfl

theorem rows_succ (L : Nat) :
    (List.range (L + 1)).reverse.map (rowL E lens) =
      rowL E lens L :: (List.range L).reverse.map (rowL E lens) := by
  simp [List.range_succ]

theorem cur_succ (L P : Nat) :
    ((List.range (P + 1)).map (E L)).reverse = E L P :: ((List.range P).map (E L)).reverse := by
  simp [List.range_succ]

theorem nlChk_sound : ∀ (ns : List Nat) (L P num iN cm sa : Nat)
    (fin : Nat → Nat → Nat → Nat → Nat → Nat → Bool),
    nlChk E lens ns L P num iN cm sa fin = true →
      (∀ n ∈ ns, n < 128) ∧ ∃ L' P' num' iN' cm' sa', fin L' P' num' iN' cm' sa' = true ∧
        ns.foldl nlStepL (stN E lens L P num iN cm sa) = stN E lens L' P' num' iN' cm' sa'
  | [], L, P, num, iN, cm, sa, fin, h => ⟨by simp, L, P, num, iN, cm, sa, h, rfl⟩
  | n :: ns, L, P, num, iN, cm, sa, fin, h => by
    rw [nlChk_cons] at h
    simp only [bif'_eq, forceN_eq, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, Bool.and_eq_true,
      decide_eq_true_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.succ_eq_add_one] at h
    split_ifs at h with h128 hcm h10 hat hd hi he h10' hP h10'' hP0 hPL
    all_goals try exact (Bool.false_ne_true h).elim
    all_goals
      obtain ⟨hasc, L', P', num', iN', cm', sa', hf, hfold⟩ := nlChk_sound ns _ _ _ _ _ _ fin h
      refine ⟨fun m hm => ?_, L', P', num', iN', cm', sa', hf, ?_⟩
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact h128
        · exact hasc m hm
      · rw [List.foldl_cons, ← hfold]
        congr 1
        clear hfold hf h hasc
        try simp only [rowL] at *
        by_cases hs : sa = 1 <;>
        first
          | (simp_all [nlStepL, stN, rowL, List.range_succ]; done)
          | (rw [← hP]; simp_all [nlStepL, stN, rowL, List.range_succ]; done)
          | (simp_all [nlStepL, stN, rowL, List.range_succ]
             rw [← hP, List.range_succ]
             simp [he]; done)
          | (simp_all [nlStepL, stN, rowL, List.range_succ]
             rw [if_neg (by omega)]
             simp [hi])

theorem nlLines_of_chk {ns : List Nat} {nl : Nat}
    (h : nlChk E lens ns 0 0 0 0 0 1 (nlEnd nl) = true) :
    (∀ n ∈ ns, n < 128) ∧ nlLines ns = (List.range nl).map (rowL E lens) := by
  obtain ⟨hasc, L', P', num', iN', cm', sa', hf, hfold⟩ := nlChk_sound E lens ns 0 0 0 0 0 1 _ h
  refine ⟨hasc, ?_⟩
  have e0 : nlInitL = stN E lens 0 0 0 0 0 1 := rfl
  unfold nlLines
  rw [e0, hfold]
  unfold nlEnd at hf
  simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hf
  obtain ⟨rfl, rfl, hi⟩ := hf
  have hi' : (iN' == 1) = false := hi
  simp [nlFinL, stN, hi', List.map_reverse]

end Chk

theorem numLines_ofList {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    numLines (String.ofList cs) =
      ((nlLines (cs.map Char.toNat)).map fun l => (l.map UInt32.ofNat).toArray).toArray := by
  rw [numLines_eq_foldl, CFSG.KS.B32.toUTF8_toList h]
  have e : (cs.map fun c => UInt8.ofNat c.toNat) = (cs.map Char.toNat).map UInt8.ofNat := by
    simp
  have e0 : ((#[], #[], 0, false, false, true) : NLA) = toA nlInitL := by
    simp [toA, nlInitL, toArr]
  rw [e, e0, foldl_toA _ _ (by simpa using h), nlFinA_toA]
  rfl

section Chk2

variable (E : Nat → Nat → Nat) (lens : Nat → Nat)

theorem numLines_of_chk {cs : List Char} {nl : Nat}
    (h : nlChk E lens (cs.map Char.toNat) 0 0 0 0 0 1 (nlEnd nl) = true) :
    (numLines (String.ofList cs)).size = nl ∧ ∀ k < nl,
      ((numLines (String.ofList cs))[k]!).size = lens k ∧
        ∀ p < lens k, ((numLines (String.ofList cs))[k]!)[p]! = UInt32.ofNat (E k p) := by
  obtain ⟨hasc, hl⟩ := nlLines_of_chk E lens h
  have hasc' : ∀ c ∈ cs, c.toNat < 128 := fun c hc => hasc _ (List.mem_map_of_mem hc)
  rw [numLines_ofList hasc', hl]
  refine ⟨by simp, fun k hk => ?_⟩
  have e :
      ((((List.range nl).map (rowL E lens)).map fun l => (l.map UInt32.ofNat).toArray).toArray)[k]! =
      ((rowL E lens k).map UInt32.ofNat).toArray := by
    rw [getElem!_pos _ _ (by simpa using hk)]
    simp [hk]
  rw [e]
  refine ⟨by simp [rowL], fun p hp => ?_⟩
  rw [getElem!_pos _ _ (by simpa [rowL] using hp)]
  simp [rowL, hp]

end Chk2

end CFSG.KS.RouteP
