module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
public import Certificates.Data.CFSGNative.Timmesfeld.PcReg
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

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular

open _root_.Timmesfeld.PcReg CFSG.Sporadic.Th CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

variable {p n : ℕ} {pw cw cwR : Array (Array ℕ)}

@[expose] def wordF (n : ℕ) (v : Array ℕ) : FreeGroup (Fin n) :=
  ((List.range n).map fun k => if h : k < n then FreeGroup.of ⟨k, h⟩ ^ v[k]! else 1).prod

@[expose] def pwF (n : ℕ) (pw : Array (Array ℕ)) (i : Fin n) : FreeGroup (Fin n) :=
  wordF n pw[i.val]!

@[expose] def cwF (n : ℕ) (cw : Array (Array ℕ)) (i j : Fin n) : FreeGroup (Fin n) :=
  wordF n cw[i.val * n + j.val]!

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
