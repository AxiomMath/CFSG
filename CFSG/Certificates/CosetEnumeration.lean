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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

@[expose] def evalWord (gen : ℕ → G) (w : List ℕ) : G := (w.map gen).prod

@[simp] theorem evalWord_nil (gen : ℕ → G) : evalWord gen [] = 1 := rfl

@[simp] theorem evalWord_cons (gen : ℕ → G) (c : ℕ) (w : List ℕ) :
    evalWord gen (c :: w) = gen c * evalWord gen w := by
  simp [evalWord]

noncomputable def rep (gen : ℕ → G) (L : ℕ) (pl : ℕ → ℕ) (j : ℕ) : G :=
  if _h : 0 < j ∧ pl j / L < j then rep gen L pl (pl j / L) * gen (pl j % L) else 1
termination_by j
decreasing_by exact _h.2

theorem rep_zero (gen : ℕ → G) (L : ℕ) (pl : ℕ → ℕ) : rep gen L pl 0 = 1 := by
  rw [rep]; simp

theorem rep_eq (gen : ℕ → G) (L : ℕ) (pl : ℕ → ℕ) {j : ℕ} (hj : 0 < j) (hp : pl j / L < j) :
    rep gen L pl j = rep gen L pl (pl j / L) * gen (pl j % L) := by
  rw [rep]; simp [hj, hp]

@[expose] def wordAt : List (List ℕ) → ℕ → List ℕ
  | [], _ => []
  | w :: _, 0 => w
  | _ :: ws, n + 1 => wordAt ws n

theorem wordAt_mem {ws : List (List ℕ)} {n : ℕ} (hn : n < ws.length) : wordAt ws n ∈ ws := by
  induction ws generalizing n with
  | nil => simp at hn
  | cons w ws ih =>
    cases n with
    | zero => simp [wordAt]
    | succ n => simp only [wordAt]; exact List.mem_cons_of_mem _ (ih (by simpa using hn))

@[expose] def lettersOK (L : ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all fun w => w.all fun c => Nat.blt c L

end CFSG.Certificates.CosetEnumeration
