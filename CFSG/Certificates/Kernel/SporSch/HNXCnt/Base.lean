module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Local.HN.X.Lib
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

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] noncomputable def xv (T : Nat → Nat) (i : Nat) : Nat := fldW (getRec T 464 i) 0 399

@[expose] noncomputable def xe (T : Nat → Nat) (i j : Nat) : Nat := xv T i / 2 ^ (3 * j) % 8

@[expose] noncomputable def qv (T : Nat → Nat) (s i : Nat) : Nat :=
  fldW (getRec T 464 i) (399 + 21 * s) 21

@[expose] noncomputable def pp (T : Nat → Nat) (i : Nat) : Nat := fldW (getRec T 464 i) 441 22

@[expose] noncomputable def ent13 (W j k : Nat) : Nat := W / 2 ^ (1729 * j + 13 * k) % 2 ^ 13

@[expose] def CoreRec (T : Nat → Nat) (n MS YA YB i r : Nat) : Prop :=
  (i = 0 → pp T 0 = 0) ∧ (0 < i → pp T i ≤ 2 * i ∧ pp T (i - 1) < pp T i) ∧
  qv T 0 i < n ∧ fldW YA (1729 * r) 1729 = spread MS (xv T (qv T 0 i)) ∧
    pp T (qv T 0 i) ≤ 2 * i + 1 ∧
  qv T 1 i < n ∧ fldW YB (1729 * r) 1729 = spread MS (xv T (qv T 1 i)) ∧
    pp T (qv T 1 i) ≤ 2 * i + 2

theorem fldW_eq (r o w : Nat) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  unfold fldW
  change (r >>> o) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem loopStrictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem getRec_eq (T : Nat → Nat) (RB i : Nat) :
    getRec T RB i = T (i / 64) / 2 ^ (i % 64 * RB) % 2 ^ RB := by
  unfold getRec
  rw [loopStrictN_eq, fldW_eq]
  have e1 : Nat.shiftRight i (nat_lit 6) = i / 64 := by
    change i >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land i (nat_lit 63) = i % 64 := by
    change i &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [e1, e2]
  rfl

theorem getRec_leaf (T : Nat → Nat) (b r : Nat) (hr : r < 64) :
    getRec T 464 (64 * b + r) = T b / 2 ^ (464 * r) % 2 ^ 464 := by
  rw [getRec_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r 464]

end CFSG.KS.SporSch.HNXP

end
