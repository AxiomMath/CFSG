module

public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.CGT.T75JM

@[ext] structure Cols where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  deriving DecidableEq

@[expose] def applyC (c : Cols) (v : ℕ) : ℕ :=
  (if v.testBit 0 then c.c0 else 0) ^^^ (if v.testBit 1 then c.c1 else 0) ^^^
    (if v.testBit 2 then c.c2 else 0) ^^^ (if v.testBit 3 then c.c3 else 0)

@[expose] def Cols.col (c : Cols) : Fin 4 → ℕ
  | 0 => c.c0
  | 1 => c.c1
  | 2 => c.c2
  | 3 => c.c3

@[expose] def idC : Cols := ⟨1, 2, 4, 8⟩

@[expose] def compC (c d : Cols) : Cols :=
  ⟨applyC c d.c0, applyC c d.c1, applyC c d.c2, applyC c d.c3⟩

@[expose] def powC (c : Cols) : ℕ → Cols
  | 0 => idC
  | n + 1 => compC c (powC c n)

theorem applyC_xor (c : Cols) (u w : ℕ) : applyC c (u ^^^ w) = applyC c u ^^^ applyC c w := by
  unfold applyC
  simp only [Nat.testBit_xor]
  cases u.testBit 0 <;> cases w.testBit 0 <;> cases u.testBit 1 <;> cases w.testBit 1 <;>
    cases u.testBit 2 <;> cases w.testBit 2 <;> cases u.testBit 3 <;> cases w.testBit 3 <;>
    simp [Nat.xor_comm, Nat.xor_left_comm]

theorem applyC_zero (c : Cols) : applyC c 0 = 0 := by simp [applyC]

theorem vec_eq {v : ℕ} (hv : v < 16) :
    v = ((if v.testBit 0 then 1 else 0) ^^^ (if v.testBit 1 then 2 else 0)) ^^^
      ((if v.testBit 2 then 4 else 0) ^^^ (if v.testBit 3 then 8 else 0)) := by
  interval_cases v <;> decide

theorem applyC_idC {v : ℕ} (hv : v < 16) : applyC idC v = v := by
  interval_cases v <;> decide

theorem applyC_basis (c : Cols) (i : Fin 4) : applyC c (2 ^ i.val) = c.col i := by
  fin_cases i <;> simp (config := {decide := true}) [applyC, Cols.col]

theorem applyC_compC (c d : Cols) (v : ℕ) :
    applyC (compC c d) v = applyC c (applyC d v) := by
  have e : ∀ (x : ℕ) (b : Bool), applyC c (if b then x else 0) =
      if b then applyC c x else 0 := fun x b => by cases b <;> simp [applyC_zero]
  have hd : applyC d v = ((((if v.testBit 0 then d.c0 else 0) ^^^
      (if v.testBit 1 then d.c1 else 0)) ^^^ (if v.testBit 2 then d.c2 else 0)) ^^^
      (if v.testBit 3 then d.c3 else 0)) := rfl
  rw [hd, applyC_xor, applyC_xor, applyC_xor, e, e, e, e]
  rfl

theorem compC_idC (c : Cols) : compC c idC = c := by
  have h0 : applyC c 1 = c.c0 := by simp (config := {decide := true}) [applyC]
  have h1 : applyC c 2 = c.c1 := by simp (config := {decide := true}) [applyC]
  have h2 : applyC c 4 = c.c2 := by simp (config := {decide := true}) [applyC]
  have h3 : applyC c 8 = c.c3 := by simp (config := {decide := true}) [applyC]
  simp only [compC, idC, h0, h1, h2, h3]

theorem applyC_lt {c : Cols} (hc : ∀ i, c.col i < 16) (v : ℕ) : applyC c v < 16 := by
  have key : ∀ (a b : ℕ), a < 16 → b < 16 → a ^^^ b < 16 := fun a b ha hb =>
    Nat.xor_lt_two_pow (n := 4) ha hb
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  have z : (0 : ℕ) < 16 := by norm_num
  unfold applyC
  refine key _ _ (key _ _ (key _ _ ?_ ?_) ?_) ?_ <;> split <;> assumption

end CFSG.CGT.T75JM
