module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowCheck
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

namespace CFSG.EvenSporadicStandard.M23Std.FusionCheck

open CFSG.EvenSporadicStandard.Wong77.M23Sylow

@[expose] def tWordS : List Nat := [3, 5, 6]

@[expose] def tTab : Tab := wordTab gensTab tWordS

@[expose] def invWords : List (List Nat) := [[4, 84], [32], [16], [8], [4], [2], [1]]

@[expose] def mWord : List Nat :=
  [
    2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0,
    1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2,
    2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0, 1, 0, 2, 0
  ]

@[expose] def bWords : List (List Nat) :=
  [
    [
      2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1,
      0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0
    ],
    [
      0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2,
      0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2,
      2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1
    ],
    [
      2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0,
      1, 1, 0, 1, 0, 1, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2
    ],
    [
      2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1
    ],
    [
      2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0,
      1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2,
      0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0
    ],
    [
      0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1,
      0, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1
    ],
    [
      1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1,
      1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0,
      2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1
    ],
    [
      1, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 2, 0, 2, 2, 0, 1,
      0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1,
      0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1
    ],
    [
      2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0,
      2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
      0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0
    ],
    [],
    [
      0, 1, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
      0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2,
      2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1
    ],
    [
      0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1,
      0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2
    ],
    [
      2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1,
      0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 1
    ],
    [
      2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0,
      1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 2, 0, 2, 2,
      0, 2, 0, 1
    ],
    [
      2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1,
      0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2
    ]
  ]

@[expose] def mTab : Tab := wordTab letterTabs mWord

@[expose] def bTab (i : Nat) : Tab := wordTab letterTabs (bWords.getD i [])

@[expose] def normOK (A : List Tab) (g : Tab) : Bool :=
  A.all fun x => A.any fun y => decide (tmul g x = tmul y g)

@[expose] def fusionCheck : Bool :=
  decide (isInv tTab = true ∧ (∀ g ∈ gensTab, comm tTab g = true) ∧
    (∀ y ∈ span gensTab, (∀ g ∈ gensTab, comm y g = true) → y = idTab ∨ y = tTab)) &&
  decide (invWords.length = 7 ∧ ∀ i : Fin 7, (∀ j ∈ invWords.getD i [],
      isInv ((span gensTab).getD j idTab) = true) ∧
      wordTab (span gensTab) (invWords.getD i []) = gensTab.getD i idTab) &&
  decide (∀ k : Fin 2, (∀ g ∈ gensTab, normOK (elemTabs k) g = true) ∧ tTab ∈ elemTabs k ∧
    normOK (elemTabs k) mTab = true) &&
  decide (comm mTab tTab = false) &&
  decide (bWords.length = 15 ∧ ∀ i : Fin 15, normOK (elemTabs 1) (bTab i) = true ∧
    tmul (bTab i) tTab = tmul ((elemTabs 1).getD i idTab) (bTab i))

end CFSG.EvenSporadicStandard.M23Std.FusionCheck
