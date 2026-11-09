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

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Matrix

namespace D4

abbrev M8 := Matrix (Fin 8) (Fin 8) ℤ

@[expose] def E (r s : Fin 8) : M8 := Matrix.single r s 1

@[expose] def W (a b : Fin 8) : M8 := E a b - E b a

@[expose] def cartanD4 : Matrix (Fin 4) (Fin 4) ℤ := !![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2]

@[expose] def e (i : Fin 4) : Fin 4 → ℤ := Pi.single i 1

@[expose] def XZ : Fin 4 → M8
  | 0 => -E 0 1 + E 5 4
  | 1 => -E 2 3 + E 7 6
  | 2 => -E 1 2 + E 6 5
  | 3 => -E 2 7 + E 3 6

@[expose] def YZ (i : Fin 4) : M8 := (XZ i)ᵀ

@[expose] def HZ : Fin 4 → M8
  | 0 => W 0 4 - W 1 5
  | 1 => W 2 6 - W 3 7
  | 2 => -W 1 5 + W 2 6
  | 3 => W 2 6 + W 3 7

@[expose] def d4Roots : List (Fin 4 → ℤ) :=
  [![1, 1, 2, 1],
   ![1, 1, 1, 1],
   ![0, 1, 1, 1],
   ![1, 0, 1, 1],
   ![1, 1, 1, 0],
   ![0, 0, 1, 1],
   ![0, 1, 1, 0],
   ![1, 0, 1, 0],
   ![0, 0, 0, 1],
   ![0, 0, 1, 0],
   ![0, 1, 0, 0],
   ![1, 0, 0, 0],
   ![-1, 0, 0, 0],
   ![0, -1, 0, 0],
   ![0, 0, -1, 0],
   ![0, 0, 0, -1],
   ![-1, 0, -1, 0],
   ![0, -1, -1, 0],
   ![0, 0, -1, -1],
   ![-1, -1, -1, 0],
   ![-1, 0, -1, -1],
   ![0, -1, -1, -1],
   ![-1, -1, -1, -1],
   ![-1, -1, -2, -1]]

@[expose] def phiRootAux (β : Fin 4 → ℤ) : M8 :=
  if β = ![1, 1, 2, 1] then W 0 1
  else if β = ![1, 1, 1, 1] then -W 0 2
  else if β = ![0, 1, 1, 1] then W 1 2
  else if β = ![1, 0, 1, 1] then W 0 3
  else if β = ![1, 1, 1, 0] then W 0 7
  else if β = ![0, 0, 1, 1] then -W 1 3
  else if β = ![0, 1, 1, 0] then -W 1 7
  else if β = ![1, 0, 1, 0] then W 0 6
  else if β = ![0, 0, 0, 1] then W 2 3
  else if β = ![0, 0, 1, 0] then -W 1 6
  else if β = ![0, 1, 0, 0] then W 2 7
  else if β = ![1, 0, 0, 0] then W 0 5
  else if β = ![-1, 0, 0, 0] then -W 1 4
  else if β = ![0, -1, 0, 0] then -W 3 6
  else if β = ![0, 0, -1, 0] then W 2 5
  else if β = ![0, 0, 0, -1] then W 6 7
  else if β = ![-1, 0, -1, 0] then W 2 4
  else if β = ![0, -1, -1, 0] then -W 3 5
  else if β = ![0, 0, -1, -1] then W 5 7
  else if β = ![-1, -1, -1, 0] then -W 3 4
  else if β = ![-1, 0, -1, -1] then W 4 7
  else if β = ![0, -1, -1, -1] then W 5 6
  else if β = ![-1, -1, -1, -1] then W 4 6
  else if β = ![-1, -1, -2, -1] then W 4 5
  else 0

@[expose] def phiRootZ (β : Fin 4 → ℤ) : M8 := if β ∈ d4Roots then phiRootAux β else 0

@[expose] def BZ : M8 := Matrix.of fun r s => if (r.val + 4 = s.val) ∨ (s.val + 4 = r.val) then 1 else 0

theorem XZ_sq : ∀ i : Fin 4, XZ i * XZ i = 0 := by decide +kernel

theorem YZ_sq : ∀ i : Fin 4, YZ i * YZ i = 0 := by decide +kernel

theorem phiRootZ_not_root {β : Fin 4 → ℤ} (hβ : β ∉ d4Roots) : phiRootZ β = 0 := if_neg hβ

private theorem tableX_123 :
    (∀ i j : Fin 4, XZ i * HZ j + HZ j * (XZ i)ᵀ = ((cartanD4 j i).natAbs : ℤ) • phiRootZ (e i) ∧
      XZ i * HZ j * (XZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, XZ i * phiRootZ (e i) + phiRootZ (e i) * (XZ i)ᵀ = 0 ∧
      XZ i * phiRootZ (e i) * (XZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, XZ i * phiRootZ (-e i) + phiRootZ (-e i) * (XZ i)ᵀ = HZ i ∧
      XZ i * phiRootZ (-e i) * (XZ i)ᵀ = phiRootZ (e i)) := by
  decide +kernel

private theorem tableX_4_0 : ∀ α ∈ d4Roots, α ≠ e 0 → α ≠ -e 0 →
      XZ 0 * phiRootZ α + phiRootZ α * (XZ 0)ᵀ = phiRootZ (α + e 0) ∧
      XZ 0 * phiRootZ α * (XZ 0)ᵀ = 0 := by
  decide +kernel

private theorem tableX_4_1 : ∀ α ∈ d4Roots, α ≠ e 1 → α ≠ -e 1 →
      XZ 1 * phiRootZ α + phiRootZ α * (XZ 1)ᵀ = phiRootZ (α + e 1) ∧
      XZ 1 * phiRootZ α * (XZ 1)ᵀ = 0 := by
  decide +kernel

private theorem tableX_4_2 : ∀ α ∈ d4Roots, α ≠ e 2 → α ≠ -e 2 →
      XZ 2 * phiRootZ α + phiRootZ α * (XZ 2)ᵀ = phiRootZ (α + e 2) ∧
      XZ 2 * phiRootZ α * (XZ 2)ᵀ = 0 := by
  decide +kernel

private theorem tableX_4_3 : ∀ α ∈ d4Roots, α ≠ e 3 → α ≠ -e 3 →
      XZ 3 * phiRootZ α + phiRootZ α * (XZ 3)ᵀ = phiRootZ (α + e 3) ∧
      XZ 3 * phiRootZ α * (XZ 3)ᵀ = 0 := by
  decide +kernel

theorem tableX :
    (∀ i j : Fin 4, XZ i * HZ j + HZ j * (XZ i)ᵀ = ((cartanD4 j i).natAbs : ℤ) • phiRootZ (e i) ∧
      XZ i * HZ j * (XZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, XZ i * phiRootZ (e i) + phiRootZ (e i) * (XZ i)ᵀ = 0 ∧
      XZ i * phiRootZ (e i) * (XZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, XZ i * phiRootZ (-e i) + phiRootZ (-e i) * (XZ i)ᵀ = HZ i ∧
      XZ i * phiRootZ (-e i) * (XZ i)ᵀ = phiRootZ (e i)) ∧
    (∀ i : Fin 4, ∀ α ∈ d4Roots, α ≠ e i → α ≠ -e i →
      XZ i * phiRootZ α + phiRootZ α * (XZ i)ᵀ = phiRootZ (α + e i) ∧
      XZ i * phiRootZ α * (XZ i)ᵀ = 0) :=
  ⟨tableX_123.1, tableX_123.2.1, tableX_123.2.2, fun i => by
    fin_cases i
    exacts [tableX_4_0, tableX_4_1, tableX_4_2, tableX_4_3]⟩

private theorem tableY_123 :
    (∀ i j : Fin 4, YZ i * HZ j + HZ j * (YZ i)ᵀ = ((cartanD4 j i).natAbs : ℤ) • phiRootZ (-e i) ∧
      YZ i * HZ j * (YZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, YZ i * phiRootZ (-e i) + phiRootZ (-e i) * (YZ i)ᵀ = 0 ∧
      YZ i * phiRootZ (-e i) * (YZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, YZ i * phiRootZ (e i) + phiRootZ (e i) * (YZ i)ᵀ = HZ i ∧
      YZ i * phiRootZ (e i) * (YZ i)ᵀ = phiRootZ (-e i)) := by
  decide +kernel

private theorem tableY_4_0 : ∀ α ∈ d4Roots, α ≠ e 0 → α ≠ -e 0 →
      YZ 0 * phiRootZ α + phiRootZ α * (YZ 0)ᵀ = phiRootZ (α - e 0) ∧
      YZ 0 * phiRootZ α * (YZ 0)ᵀ = 0 := by
  decide +kernel

private theorem tableY_4_1 : ∀ α ∈ d4Roots, α ≠ e 1 → α ≠ -e 1 →
      YZ 1 * phiRootZ α + phiRootZ α * (YZ 1)ᵀ = phiRootZ (α - e 1) ∧
      YZ 1 * phiRootZ α * (YZ 1)ᵀ = 0 := by
  decide +kernel

private theorem tableY_4_2 : ∀ α ∈ d4Roots, α ≠ e 2 → α ≠ -e 2 →
      YZ 2 * phiRootZ α + phiRootZ α * (YZ 2)ᵀ = phiRootZ (α - e 2) ∧
      YZ 2 * phiRootZ α * (YZ 2)ᵀ = 0 := by
  decide +kernel

private theorem tableY_4_3 : ∀ α ∈ d4Roots, α ≠ e 3 → α ≠ -e 3 →
      YZ 3 * phiRootZ α + phiRootZ α * (YZ 3)ᵀ = phiRootZ (α - e 3) ∧
      YZ 3 * phiRootZ α * (YZ 3)ᵀ = 0 := by
  decide +kernel

theorem tableY :
    (∀ i j : Fin 4, YZ i * HZ j + HZ j * (YZ i)ᵀ = ((cartanD4 j i).natAbs : ℤ) • phiRootZ (-e i) ∧
      YZ i * HZ j * (YZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, YZ i * phiRootZ (-e i) + phiRootZ (-e i) * (YZ i)ᵀ = 0 ∧
      YZ i * phiRootZ (-e i) * (YZ i)ᵀ = 0) ∧
    (∀ i : Fin 4, YZ i * phiRootZ (e i) + phiRootZ (e i) * (YZ i)ᵀ = HZ i ∧
      YZ i * phiRootZ (e i) * (YZ i)ᵀ = phiRootZ (-e i)) ∧
    (∀ i : Fin 4, ∀ α ∈ d4Roots, α ≠ e i → α ≠ -e i →
      YZ i * phiRootZ α + phiRootZ α * (YZ i)ᵀ = phiRootZ (α - e i) ∧
      YZ i * phiRootZ α * (YZ i)ᵀ = 0) :=
  ⟨tableY_123.1, tableY_123.2.1, tableY_123.2.2, fun i => by
    fin_cases i
    exacts [tableY_4_0, tableY_4_1, tableY_4_2, tableY_4_3]⟩

theorem tableB : ∀ i : Fin 4, ((XZ i)ᵀ * BZ + BZ * XZ i = 0 ∧ (XZ i)ᵀ * BZ * XZ i = 0) ∧
    ((YZ i)ᵀ * BZ + BZ * YZ i = 0 ∧ (YZ i)ᵀ * BZ * YZ i = 0) := by
  decide +kernel

end D4

end CFSG.ComponentClassification.CatFC.KGHS3
