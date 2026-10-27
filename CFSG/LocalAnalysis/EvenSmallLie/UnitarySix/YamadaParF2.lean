module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem bz_true : bz true = 1 := rfl

@[simp] theorem bz_false : bz false = 0 := rfl

theorem bz_xor (x y : Bool) : bz (x ^^ y) = bz x + bz y := by
  cases x <;> cases y <;> decide

theorem bz_and (x y : Bool) : bz (x && y) = bz x * bz y := by
  cases x <;> cases y <;> decide

theorem bz_beq_one (a : ZMod 2) : bz (a == 1) = a := by
  fin_cases a <;> rfl

@[expose] def xorFold (k : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range k).foldl (fun acc j => acc ^^ f j) false

theorem xorFold_succ (k : ℕ) (f : ℕ → Bool) : xorFold (k + 1) f = (xorFold k f ^^ f k) := by
  rw [xorFold, List.range_succ, List.foldl_append]
  rfl

theorem bz_xorFold (k : ℕ) (f : ℕ → Bool) : bz (xorFold k f) = ∑ j : Fin k, bz (f j) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [xorFold_succ, bz_xor, ih, Fin.sum_univ_castSucc]; rfl

@[expose] def bitsOfAux (f : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | i, k + 1, acc => bitsOfAux f (i + 1) k (if f i then acc ||| 2 ^ i else acc)

@[expose] def bitsOf (n : ℕ) (f : ℕ → Bool) : ℕ := bitsOfAux f 0 n 0

theorem testBit_bitsOfAux (f : ℕ → Bool) (i k acc j : ℕ) :
    (bitsOfAux f i k acc).testBit j = (acc.testBit j || (decide (i ≤ j ∧ j < i + k) && f j)) := by
  induction k generalizing i acc with
  | zero => simp [bitsOfAux]
  | succ k ih =>
    rw [bitsOfAux, ih]
    have e1 : (decide (i + 1 ≤ j ∧ j < i + 1 + k)) =
        (decide (i ≤ j ∧ j < i + (k + 1)) && !decide (j = i)) := by
      by_cases hj : j = i
      · subst hj; simp
      · simp only [hj, decide_false, Bool.not_false, Bool.and_true]
        apply decide_eq_decide.mpr; omega
    rw [e1]
    by_cases hj : j = i
    · subst hj
      by_cases hf : f j <;> simp [hf, Nat.testBit_or]
    · have hj' : i ≠ j := Ne.symm hj
      split_ifs <;> simp [Nat.testBit_or, hj, hj']

theorem testBit_bitsOf (n : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (bitsOf n f).testBit j = (decide (j < n) && f j) := by
  rw [bitsOf, testBit_bitsOfAux]
  simp

@[expose] def toVec (n v : ℕ) : Fin n → ZMod 2 := fun j => bz (v.testBit j)

@[expose] def toMat (n m : ℕ) (A : Array ℕ) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => bz ((A.getD i 0).testBit j)

theorem toMat_apply (n m : ℕ) (A : Array ℕ) (i : Fin n) (j : Fin m) :
    toMat n m A i j = bz ((A.getD i 0).testBit j) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : (Array.ofFn f).getD i 0 = f i := by
  simp [Array.getD_eq_getD_getElem?]

@[expose] def rowMul (k a : ℕ) (B : Array ℕ) : ℕ :=
  (List.range k).foldl (fun acc l => if a.testBit l then acc ^^^ B.getD l 0 else acc) 0

theorem rowMul_succ (k a : ℕ) (B : Array ℕ) :
    rowMul (k + 1) a B = if a.testBit k then rowMul k a B ^^^ B.getD k 0 else rowMul k a B := by
  rw [rowMul, List.range_succ, List.foldl_append]
  rfl

theorem testBit_rowMul (k a : ℕ) (B : Array ℕ) (j : ℕ) :
    (rowMul k a B).testBit j = xorFold k fun l => a.testBit l && (B.getD l 0).testBit j := by
  induction k with
  | zero => simp [rowMul, xorFold]
  | succ k ih =>
    rw [rowMul_succ, xorFold_succ, ← ih]
    cases a.testBit k <;> simp [Nat.testBit_xor]

@[expose] def bmul (n k : ℕ) (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := n) fun i => rowMul k (A.getD i 0) B

theorem toMat_bmul (n k m : ℕ) (A B : Array ℕ) :
    toMat n m (bmul n k A B) = toMat n k A * toMat k m B := by
  ext i j
  rw [toMat_apply, bmul, getD_ofFn, testBit_rowMul, bz_xorFold, mul_apply]
  simp only [bz_and, toMat_apply]

@[expose] def bxor (n : ℕ) (A B : Array ℕ) : Array ℕ :=
  Array.ofFn (n := n) fun i => A.getD i 0 ^^^ B.getD i 0

theorem toMat_bxor (n m : ℕ) (A B : Array ℕ) :
    toMat n m (bxor n A B) = toMat n m A + toMat n m B := by
  ext i j
  simp only [toMat_apply, bxor, getD_ofFn, Nat.testBit_xor, bz_xor, Matrix.add_apply]

@[expose] def btr (n m : ℕ) (A : Array ℕ) : Array ℕ :=
  Array.ofFn (n := m) fun j => bitsOf n fun i => (A.getD i 0).testBit j

theorem toMat_btr (n m : ℕ) (A : Array ℕ) : toMat m n (btr n m A) = (toMat n m A)ᵀ := by
  ext j i
  simp [toMat_apply, btr, testBit_bitsOf]

@[expose] def matBits (n m : ℕ) (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Array ℕ :=
  Array.ofFn (n := n) fun i => bitsOf m fun j => if h : j < m then M i ⟨j, h⟩ == 1 else false

theorem toMat_matBits (n m : ℕ) (M : Matrix (Fin n) (Fin m) (ZMod 2)) :
    toMat n m (matBits n m M) = M := by
  ext i j
  simp [toMat_apply, matBits, testBit_bitsOf, bz_beq_one]

@[expose] def bmulVec (n m : ℕ) (A : Array ℕ) (v : ℕ) : ℕ :=
  bitsOf n fun i => xorFold m fun j => (A.getD i 0).testBit j && v.testBit j

theorem toVec_bmulVec (n m : ℕ) (A : Array ℕ) (v : ℕ) :
    toVec n (bmulVec n m A v) = toMat n m A *ᵥ toVec m v := by
  ext i
  simp only [toVec, bmulVec, testBit_bitsOf, i.isLt, decide_true, Bool.true_and, bz_xorFold,
    bz_and, mulVec, dotProduct, toMat_apply]

@[expose] def bIsId (n : ℕ) (X : Array ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => (X.getD i 0).testBit j == decide (i = j)

theorem toMat_eq_one_of_bIsId {n : ℕ} {X : Array ℕ} (h : bIsId n X = true) : toMat n n X = 1 := by
  ext i j
  simp only [bIsId, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [toMat_apply, h i i.isLt j j.isLt, one_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Fin.val_ne_of_ne hij]

theorem eq_mulVec_of_cert {n m p : ℕ} {R : Matrix (Fin p) (Fin n) (ZMod 2)}
    {B : Matrix (Fin n) (Fin m) (ZMod 2)} {E : Matrix (Fin m) (Fin n) (ZMod 2)}
    {Q : Matrix (Fin n) (Fin p) (ZMod 2)} (h : B * E + Q * R = 1) {c : Fin n → ZMod 2}
    (hc : R *ᵥ c = 0) : c = B *ᵥ (E *ᵥ c) := by
  have e := congrArg (· *ᵥ c) h
  simp only [add_mulVec, ← mulVec_mulVec, hc, mulVec_zero, add_zero, one_mulVec] at e
  exact e.symm

theorem eq_zero_of_cert {n p : ℕ} {R : Matrix (Fin p) (Fin n) (ZMod 2)}
    {Q : Matrix (Fin n) (Fin p) (ZMod 2)} (h : Q * R = 1) {c : Fin n → ZMod 2}
    (hc : R *ᵥ c = 0) : c = 0 := by
  have e := congrArg (· *ᵥ c) h
  simp only [← mulVec_mulVec, hc, mulVec_zero, one_mulVec] at e
  exact e.symm

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
