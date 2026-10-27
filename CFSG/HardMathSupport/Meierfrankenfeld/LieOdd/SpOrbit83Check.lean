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

open Matrix

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

@[expose] def Afam : Fin 29 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![
  !![2, 0, 1, 0; 1, 0, 2, 1; 1, 2, 2, 0; 2, 2, 0, 2],
  !![2, 2, 2, 0; 1, 2, 0, 1; 0, 1, 1, 2; 0, 1, 0, 1],
  !![1, 0, 2, 2; 1, 1, 0, 2; 0, 1, 0, 2; 2, 1, 2, 0],
  !![2, 2, 0, 1; 0, 2, 1, 1; 2, 2, 2, 1; 1, 2, 1, 2],
  !![0, 0, 1, 1; 0, 0, 0, 2; 1, 0, 0, 1; 1, 2, 2, 1],
  !![0, 2, 0, 0; 2, 2, 0, 2; 2, 0, 1, 0; 1, 0, 2, 2],
  !![1, 0, 2, 1; 0, 0, 1, 0; 1, 1, 2, 0; 0, 2, 1, 0],
  !![2, 2, 1, 0; 2, 2, 2, 2; 2, 0, 0, 0; 1, 2, 0, 0],
  !![0, 2, 2, 2; 2, 0, 1, 0; 1, 0, 0, 2; 1, 2, 1, 0],
  !![2, 1, 2, 2; 2, 2, 0, 0; 0, 1, 1, 0; 0, 2, 1, 2],
  !![0, 1, 2, 1; 1, 1, 0, 1; 1, 2, 2, 0; 0, 1, 1, 0],
  !![2, 1, 2, 2; 2, 2, 2, 2; 2, 1, 1, 0; 2, 0, 1, 2],
  !![0, 1, 0, 2; 1, 1, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0],
  !![2, 1, 1, 2; 2, 1, 0, 1; 1, 2, 1, 1; 1, 0, 1, 1],
  !![2, 0, 1, 2; 1, 2, 2, 1; 0, 2, 1, 2; 2, 0, 0, 1],
  !![2, 1, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 2, 2, 2, 0],
  !![2, 0, 2, 0; 2, 2, 0, 2; 1, 1, 2, 2; 2, 0, 0, 1],
  !![1, 0, 0, 0; 2, 1, 2, 0; 1, 2, 2, 1; 1, 2, 1, 2],
  !![0, 1, 2, 0; 0, 2, 2, 0; 2, 1, 1, 1; 1, 1, 2, 1],
  !![1, 2, 1, 1; 1, 0, 0, 1; 0, 1, 2, 2; 1, 0, 1, 1],
  !![1, 2, 0, 0; 2, 1, 2, 0; 0, 0, 0, 1; 2, 0, 1, 0],
  !![0, 1, 2, 1; 1, 0, 2, 2; 0, 1, 0, 1; 2, 0, 1, 0],
  !![2, 1, 2, 1; 1, 0, 1, 2; 2, 0, 2, 0; 1, 2, 2, 0],
  !![2, 1, 2, 0; 1, 1, 1, 0; 2, 0, 1, 0; 0, 2, 1, 1],
  !![0, 1, 2, 2; 1, 0, 2, 1; 0, 0, 1, 0; 1, 0, 0, 2],
  !![0, 1, 1, 0; 0, 2, 1, 1; 2, 0, 1, 1; 0, 2, 2, 1],
  !![0, 2, 0, 1; 1, 0, 1, 2; 2, 1, 0, 0; 0, 2, 0, 2],
  !![2, 0, 2, 2; 2, 1, 2, 2; 1, 0, 0, 2; 0, 0, 0, 2],
  !![1, 2, 2, 0; 0, 1, 2, 2; 2, 1, 2, 1; 0, 2, 0, 1]
  ]

theorem Afam_det : ∀ i, (Afam i).det ≠ 0 := by
  decide +kernel

theorem pair_distinct : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    ∀ i j : Fin 29, i ≠ j → ∀ k : ZMod 3,
      Afam j * Matrix.diagonal ![a, b, c, d] * (Afam j)ᵀ ≠
        k • (Afam i * Matrix.diagonal ![a, b, c, d] * (Afam i)ᵀ) := by
  decide +kernel

theorem form_ne_zero : ∀ a b c d : ZMod 3, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) →
    ∀ i : Fin 29, Afam i * Matrix.diagonal ![a, b, c, d] * (Afam i)ᵀ ≠ 0 := by
  decide +kernel


end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
