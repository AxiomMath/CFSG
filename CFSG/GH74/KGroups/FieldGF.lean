module

public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.GH74.KGroups

structure GF4 where
  val : Fin 4

instance : DecidableEq GF4 := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (e ▸ rfl))

namespace GF4

@[expose] def ofNat' (n : ℕ) : GF4 := ⟨⟨n % 4, Nat.mod_lt n (by norm_num)⟩⟩

@[expose] def toNat (a : GF4) : ℕ := a.val.val

@[expose] def mulNat (a b : ℕ) : ℕ :=
  let r := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0)
  if r &&& 4 = 4 then r ^^^ 7 else r

instance : Zero GF4 := ⟨ofNat' 0⟩
instance : One GF4 := ⟨ofNat' 1⟩
instance : Add GF4 := ⟨fun a b => ofNat' (a.toNat ^^^ b.toNat)⟩
instance : Neg GF4 := ⟨fun a => a⟩
instance : Mul GF4 := ⟨fun a b => ofNat' (mulNat a.toNat b.toNat)⟩
instance : Inv GF4 := ⟨fun a => ofNat' (mulNat a.toNat a.toNat)⟩
instance : Fintype GF4 :=
  Fintype.ofEquiv (Fin 4) ⟨GF4.mk, GF4.val, fun _ => rfl, fun _ => rfl⟩

instance : Field GF4 :=
  Field.ofMinimalAxioms GF4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end GF4

structure GF16 where
  val : Fin 16

instance : DecidableEq GF16 := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun e => h (e ▸ rfl))

namespace GF16

@[expose] def ofNat' (n : ℕ) : GF16 := ⟨⟨n % 16, Nat.mod_lt n (by norm_num)⟩⟩

@[expose] def toNat (a : GF16) : ℕ := a.val.val

@[expose] def mulNat (a b : ℕ) : ℕ :=
  let r := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
    (if b &&& 4 = 4 then a <<< 2 else 0) ^^^ (if b &&& 8 = 8 then a <<< 3 else 0)
  let r := if r &&& 64 = 64 then r ^^^ 76 else r
  let r := if r &&& 32 = 32 then r ^^^ 38 else r
  if r &&& 16 = 16 then r ^^^ 19 else r

instance : Zero GF16 := ⟨ofNat' 0⟩
instance : One GF16 := ⟨ofNat' 1⟩
instance : Add GF16 := ⟨fun a b => ofNat' (a.toNat ^^^ b.toNat)⟩
instance : Neg GF16 := ⟨fun a => a⟩
instance : Mul GF16 := ⟨fun a b => ofNat' (mulNat a.toNat b.toNat)⟩
instance : Inv GF16 :=
  ⟨fun a =>
    let a2 := mulNat a.toNat a.toNat
    let a4 := mulNat a2 a2
    let a8 := mulNat a4 a4
    ofNat' (mulNat a8 (mulNat a4 a2))⟩
instance : Fintype GF16 :=
  Fintype.ofEquiv (Fin 16) ⟨GF16.mk, GF16.val, fun _ => rfl, fun _ => rfl⟩

instance : Field GF16 :=
  Field.ofMinimalAxioms GF16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end GF16

end CFSG.GH74.KGroups
