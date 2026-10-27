module

public import CFSG.CGT.PushingUpLit.A78.LQ4Fin
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

namespace CFSG.CGT.PushingUpLit.A78.LQ4

open CFSG.CGT.PushingUpLit.A78.LQ4Fin

@[expose] def Bits (n : ℕ) : Type := {v : ℕ // v < 2 ^ n}

namespace Bits

variable {n : ℕ}

instance : DecidableEq (Bits n) := inferInstanceAs (DecidableEq {v : ℕ // v < 2 ^ n})

instance : Fintype (Bits n) := Fintype.ofEquiv (Fin (2 ^ n)) (Fin.equivSubtype (n := 2 ^ n))

instance : CommGroup (Bits n) where
  mul a b := ⟨a.1 ^^^ b.1, Nat.xor_lt_two_pow a.2 b.2⟩
  one := ⟨0, Nat.two_pow_pos n⟩
  inv a := a
  mul_assoc a b c := Subtype.ext (Nat.xor_assoc _ _ _)
  one_mul a := Subtype.ext (Nat.zero_xor _)
  mul_one a := Subtype.ext (Nat.xor_zero _)
  inv_mul_cancel a := Subtype.ext (Nat.xor_self _)
  mul_comm a b := Subtype.ext (Nat.xor_comm _ _)

@[simp] theorem val_mul (a b : Bits n) : (a * b).1 = a.1 ^^^ b.1 := rfl

@[simp] theorem val_one : (1 : Bits n).1 = 0 := rfl

@[simp] theorem val_inv (a : Bits n) : (a⁻¹).1 = a.1 := rfl

theorem mul_self_eq (a : Bits n) : a * a = 1 := Subtype.ext (Nat.xor_self _)

theorem sq_eq_one (a : Bits n) : a ^ 2 = 1 := by rw [pow_two]; exact mul_self_eq a

theorem card_eq (n : ℕ) : Nat.card (Bits n) = 2 ^ n := by
  have : Nat.card (Bits n) = Nat.card (Fin (2 ^ n)) :=
    Nat.card_congr (Fin.equivSubtype (n := 2 ^ n)).symm
  simpa using this

theorem lt16 (v : Bits 4) : v.1 < 16 := by have h := v.2; simpa using h

theorem lt4 (v : Bits 2) : v.1 < 4 := by have h := v.2; simpa using h

end Bits

@[expose] def dec4 (w : ℕ) : Bits 4 :=
  ⟨w % 16, by have := Nat.mod_lt w (show 0 < 16 by decide); simpa using this⟩

theorem dec4_val {w : ℕ} (h : w < 16) : (dec4 w).1 = w := Nat.mod_eq_of_lt h

theorem dec4_val' (v : Bits 4) : dec4 v.1 = v := Subtype.ext (dec4_val v.lt16)

theorem xor_lt16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 := by
  have := Nat.xor_lt_two_pow (n := 4) (x := a) (y := b) (by simpa using ha) (by simpa using hb)
  simpa using this

theorem dec4_xor {v w : ℕ} (hv : v < 16) (hw : w < 16) : dec4 (v ^^^ w) = dec4 v * dec4 w := by
  apply Subtype.ext
  rw [dec4_val (xor_lt16 hv hw), Bits.val_mul, dec4_val hv, dec4_val hw]

theorem dec4_zero : dec4 0 = 1 := Subtype.ext rfl

@[expose] def qB (v : Bits 4) : Bits 2 := ⟨qv v.1, by simpa using qv_lt v.1 v.lt16⟩

@[simp] theorem qB_val (v : Bits 4) : (qB v).1 = qv v.1 := rfl

@[expose] def incl : Bits 2 →* Bits 4 where
  toFun v := ⟨v.1, lt_of_lt_of_le v.2 (by norm_num)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem incl_val (v : Bits 2) : (incl v).1 = v.1 := rfl

theorem incl_injective : Function.Injective incl := by
  intro a b h
  have := congrArg (fun x : Bits 4 => x.1) h
  exact Subtype.ext this

structure Coords (J : Type*) [Group J] where
  ε : J →* Bits 4
  surj : Function.Surjective ε
  ker_eq : ε.ker = Subgroup.center J
  η : ε.ker ≃* Bits 2
  sq : ∀ (j : J) (h : j ^ 2 ∈ ε.ker), (η ⟨j ^ 2, h⟩).1 = qv (ε j).1

end CFSG.CGT.PushingUpLit.A78.LQ4
