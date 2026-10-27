module

public import Aesop.BuiltinRules
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

public section

namespace CFSG.GH74.QTGen4.U42.U0Aut

@[expose] def qf (u : Nat) : Bool := (u.testBit 0 && u.testBit 2) ^^ (u.testBit 1 && u.testBit 3)

abbrev T4 : Type := Nat × Nat × Nat × Nat

@[expose] def ap (g : T4) (u : Nat) : Nat :=
  (if u.testBit 0 then g.1 else 0) ^^^ (if u.testBit 1 then g.2.1 else 0) ^^^
  (if u.testBit 2 then g.2.2.1 else 0) ^^^ (if u.testBit 3 then g.2.2.2 else 0)

@[expose] def IsIso (g : T4) : Bool := (List.range 16).all fun u => qf (ap g u) == qf u

@[expose] def comp (g h : T4) : T4 := (ap g h.1, ap g h.2.1, ap g h.2.2.1, ap g h.2.2.2)

@[expose] def one : T4 := (1, 2, 4, 8)

@[expose] def pw (g : T4) : Nat → T4
  | 0 => one
  | n+1 => comp g (pw g n)

def isoList : List T4 :=
  (List.range 16).flatMap fun a =>
    (List.range 16).flatMap fun b =>
      if qf a == qf 1 && qf b == qf 2 && qf (a ^^^ b) == qf 3 then
        (List.range 16).flatMap fun c =>
          if qf c == qf 4 && qf (a ^^^ c) == qf 5 && qf (b ^^^ c) == qf 6 &&
              qf (a ^^^ b ^^^ c) == qf 7 then
            (List.range 16).filterMap fun d => if IsIso (a, b, c, d) then some (a, b, c, d) else none
          else []
      else []

@[expose] def p3List : List T4 := isoList.filter fun g => pw g 3 == one

@[expose] def chkP3Card : Bool := p3List.length == 9

@[expose] def chkPow9 : Bool := isoList.all fun g => pw g 9 != one || pw g 3 == one

theorem chkP3Card_true : chkP3Card = true := by decide +kernel

theorem chkPow9_true : chkPow9 = true := by decide +kernel

theorem ap_u1 (a b c d : Nat) : ap (a, b, c, d) 1 = a := by simp +decide [ap]

theorem ap_u2 (a b c d : Nat) : ap (a, b, c, d) 2 = b := by simp +decide [ap]

theorem ap_u3 (a b c d : Nat) : ap (a, b, c, d) 3 = a ^^^ b := by simp +decide [ap]

theorem ap_u4 (a b c d : Nat) : ap (a, b, c, d) 4 = c := by simp +decide [ap]

theorem ap_u5 (a b c d : Nat) : ap (a, b, c, d) 5 = a ^^^ c := by simp +decide [ap]

theorem ap_u6 (a b c d : Nat) : ap (a, b, c, d) 6 = b ^^^ c := by simp +decide [ap]

theorem ap_u7 (a b c d : Nat) : ap (a, b, c, d) 7 = a ^^^ b ^^^ c := by simp +decide [ap]

theorem ap_u8 (a b c d : Nat) : ap (a, b, c, d) 8 = d := by simp +decide [ap]

theorem isoList_mem (g : T4) (ha : g.1 < 16) (hb : g.2.1 < 16) (hc : g.2.2.1 < 16)
    (hd : g.2.2.2 < 16) (h : IsIso g = true) : g ∈ isoList := by
  obtain ⟨a, b, c, d⟩ := g
  have hI := h
  unfold IsIso at hI
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hI
  have h1 := hI 1 (by decide)
  have h2 := hI 2 (by decide)
  have h3 := hI 3 (by decide)
  have h4 := hI 4 (by decide)
  have h5 := hI 5 (by decide)
  have h6 := hI 6 (by decide)
  have h7 := hI 7 (by decide)
  rw [ap_u1] at h1
  rw [ap_u2] at h2
  rw [ap_u3] at h3
  rw [ap_u4] at h4
  rw [ap_u5] at h5
  rw [ap_u6] at h6
  rw [ap_u7] at h7
  have hG1 : (qf a == qf 1 && qf b == qf 2 && qf (a ^^^ b) == qf 3) = true := by
    simp [h1, h2, h3]
  have hG2 : (qf c == qf 4 && qf (a ^^^ c) == qf 5 && qf (b ^^^ c) == qf 6 &&
      qf (a ^^^ b ^^^ c) == qf 7) = true := by
    simp [h4, h5, h6, h7]
  unfold isoList
  refine List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, ?_⟩
  try dsimp only
  refine List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, ?_⟩
  try dsimp only
  rw [if_pos hG1]
  refine List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, ?_⟩
  try dsimp only
  rw [if_pos hG2]
  refine List.mem_filterMap.2 ⟨d, List.mem_range.2 hd, ?_⟩
  try dsimp only
  rw [if_pos h]

end CFSG.GH74.QTGen4.U42.U0Aut
