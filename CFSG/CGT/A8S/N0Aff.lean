module

public import CFSG.CGT.A8S.RelData
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.A8S.N0

@[ext] structure Cols3 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  deriving DecidableEq

@[expose] def applyC3 (C : Cols3) (v : ℕ) : ℕ :=
  (v % 2 * C.c0) ^^^ (v / 2 % 2 * C.c1) ^^^ (v / 4 % 2 * C.c2)

@[expose] def Cols3.col (C : Cols3) : Fin 3 → ℕ
  | 0 => C.c0
  | 1 => C.c1
  | 2 => C.c2

@[expose] def idC3 : Cols3 := ⟨1, 2, 4⟩

@[expose] def compC3 (C D : Cols3) : Cols3 := ⟨applyC3 C D.c0, applyC3 C D.c1, applyC3 C D.c2⟩

theorem mul_mod_two_eq_ite (v c j : ℕ) : v / 2 ^ j % 2 * c = if v.testBit j then c else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]

theorem applyC3_eq_ite (C : Cols3) (v : ℕ) : applyC3 C v =
    (if v.testBit 0 then C.c0 else 0) ^^^ (if v.testBit 1 then C.c1 else 0) ^^^
      (if v.testBit 2 then C.c2 else 0) := by
  rw [← mul_mod_two_eq_ite v C.c0 0, ← mul_mod_two_eq_ite v C.c1 1,
    ← mul_mod_two_eq_ite v C.c2 2]
  simp [applyC3]

theorem applyC3_xor (C : Cols3) (u w : ℕ) :
    applyC3 C (u ^^^ w) = applyC3 C u ^^^ applyC3 C w := by
  simp only [applyC3_eq_ite, Nat.testBit_xor]
  cases u.testBit 0 <;> cases w.testBit 0 <;> cases u.testBit 1 <;> cases w.testBit 1 <;>
    cases u.testBit 2 <;> cases w.testBit 2 <;> simp [Nat.xor_comm, Nat.xor_left_comm]

theorem applyC3_zero (C : Cols3) : applyC3 C 0 = 0 := by simp [applyC3]

theorem vec_eq3 {v : ℕ} (hv : v < 8) :
    v = ((if v.testBit 0 then 1 else 0) ^^^ (if v.testBit 1 then 2 else 0)) ^^^
      (if v.testBit 2 then 4 else 0) := by
  interval_cases v <;> decide

theorem applyC3_idC3 {v : ℕ} (hv : v < 8) : applyC3 idC3 v = v := by
  interval_cases v <;> decide

theorem applyC3_basis (C : Cols3) (j : Fin 3) : applyC3 C (2 ^ j.val) = C.col j := by
  fin_cases j <;> simp [applyC3, Cols3.col]

theorem applyC3_compC3 (C D : Cols3) (v : ℕ) :
    applyC3 (compC3 C D) v = applyC3 C (applyC3 D v) := by
  have e : ∀ (x : ℕ) (b : Bool), applyC3 C (if b then x else 0) =
      if b then applyC3 C x else 0 := fun x b => by cases b <;> simp [applyC3_zero]
  rw [applyC3_eq_ite (compC3 C D), applyC3_eq_ite D, applyC3_xor, applyC3_xor, e, e, e]
  rfl

theorem applyC3_lt {C : Cols3} (hC : ∀ j, C.col j < 8) (v : ℕ) : applyC3 C v < 8 := by
  have key : ∀ a b : ℕ, a < 8 → b < 8 → a ^^^ b < 8 := fun a b ha hb =>
    Nat.xor_lt_two_pow (n := 3) ha hb
  have h0 := hC 0
  have h1 := hC 1
  have h2 := hC 2
  simp only [Cols3.col] at h0 h1 h2
  rw [applyC3_eq_ite]
  refine key _ _ (key _ _ ?_ ?_) ?_ <;> split <;> omega

theorem cols3_ext {A B : Cols3} (h : ∀ j : Fin 3, applyC3 A (2 ^ j.val) = applyC3 B (2 ^ j.val)) :
    A = B := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [applyC3_basis, applyC3_basis] at h0 h1 h2
  exact Cols3.ext h0 h1 h2

@[expose] def isGL3 (C : Cols3) : Bool := (List.range 7).all fun v => applyC3 C (v + 1) != 0

@[expose] def colsOfCode3 (n : ℕ) : Cols3 := ⟨n % 8, n / 8 % 8, n / 64 % 8⟩

@[expose] def allCols3 : List Cols3 := (List.range 512).map colsOfCode3

theorem length_filter_isGL3 : (allCols3.filter isGL3).length = 168 := by decide +kernel

theorem mem_allCols3 {C : Cols3} (hC : ∀ j, C.col j < 8) : C ∈ allCols3 := by
  obtain ⟨a, b, d⟩ := C
  have ha := hC 0
  have hb := hC 1
  have hd := hC 2
  simp only [Cols3.col] at ha hb hd
  refine List.mem_map.2 ⟨a + 8 * b + 64 * d, List.mem_range.2 (by omega), ?_⟩
  simp only [colsOfCode3, Cols3.mk.injEq]
  omega

@[expose] def modelCols3 (i : ℕ) : Cols3 := if i = 0 then ⟨1, 2, 5⟩ else ⟨4, 1, 2⟩

@[expose] def modelInv3 (i : ℕ) : Cols3 := if i = 0 then ⟨1, 2, 5⟩ else ⟨2, 4, 1⟩

theorem modelInv3_applyC3 :
    ∀ i < 2, ∀ v < 8, applyC3 (modelInv3 i) (applyC3 (modelCols3 i) v) = v := by
  decide

theorem modelCols3_lt : ∀ i < 2, ∀ j : Fin 3, (modelCols3 i).col j < 8 := by decide

theorem isGL3_modelCols3 : ∀ i < 2, isGL3 (modelCols3 i) = true := by decide

@[expose] def affStep (a : Fin 5 × Bool) (p : ℕ × Cols3) : ℕ × Cols3 :=
  if a.1.val < 2 then
    (applyC3 (if a.2 then modelCols3 a.1.val else modelInv3 a.1.val) p.1,
      compC3 (if a.2 then modelCols3 a.1.val else modelInv3 a.1.val) p.2)
  else (1 <<< (a.1.val - 2) ^^^ p.1, p.2)

@[expose] def affEval (w : List (Fin 5 × Bool)) : ℕ × Cols3 := w.foldr affStep (0, idC3)

@[expose] def affCode (p : ℕ × Cols3) : ℕ := p.1 + 8 * p.2.c0 + 64 * p.2.c1 + 512 * p.2.c2

theorem affEval_nil : affEval [] = (0, idC3) := rfl

theorem affEval_cons (a : Fin 5 × Bool) (w : List (Fin 5 × Bool)) :
    affEval (a :: w) = affStep a (affEval w) := rfl

theorem affEval_relsN0A8 : ∀ r ∈ relsN0A8, affEval r = (0, idC3) := by decide +kernel

@[expose] def natEqB (n m : ℕ) : Bool := Nat.beq n m

theorem eq_of_natEqB {n m : ℕ} (h : natEqB n m = true) : n = m := Nat.eq_of_beq_eq_true h

@[expose] def bitsNodup : ℕ → List ℕ → Bool
  | _, [] => true
  | m, a :: l => !m.testBit a && bitsNodup (m ||| 1 <<< a) l

theorem nodup_of_bitsNodup : ∀ {m : ℕ} {l : List ℕ}, bitsNodup m l = true →
    l.Nodup ∧ ∀ a ∈ l, m.testBit a = false
  | _, [], _ => ⟨List.nodup_nil, by simp⟩
  | m, a :: l, h => by
    simp only [bitsNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hnd, hm⟩ := nodup_of_bitsNodup h2
    refine ⟨List.nodup_cons.2 ⟨fun ha => ?_, hnd⟩, fun b hb => ?_⟩
    · have := hm a ha
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact Bool.noConfusion this
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h1
      · have := hm b hb
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

end CFSG.CGT.A8S.N0
