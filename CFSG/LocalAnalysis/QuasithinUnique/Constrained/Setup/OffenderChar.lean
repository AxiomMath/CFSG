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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.Offender

theorem char_two_add_self (F : Type*) [Field F] [CharP F 2] {W : Type*} [AddCommGroup W]
    [Module F W] (w : W) : w + w = 0 := by
  rw [← two_smul F w, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_smul]

theorem neg_eq_self_of_char_two_module (F : Type*) [Field F] [CharP F 2] {W : Type*}
    [AddCommGroup W] [Module F W] (w : W) : -w = w :=
  neg_eq_of_add_eq_zero_right (char_two_add_self F w)

theorem charP_two_of_card_two (k : Type*) [Field k] (hk : Nat.card k = 2) : CharP k 2 := by
  have h2 : (2 : k) = 0 := by
    have := card_nsmul_eq_zero' (G := k) (x := (1 : k))
    rw [hk] at this
    simpa using this
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2

theorem eq_one_of_ne_zero_of_card_two (k : Type*) [Field k] (hk : Nat.card k = 2) {c : k}
    (hc : c ≠ 0) : c = 1 := by
  obtain ⟨x, y, -, hxy'⟩ := Nat.card_eq_two_iff.1 hk
  have h0 : (0 : k) ∈ ({x, y} : Set k) := by rw [hxy']; trivial
  have h1 : (1 : k) ∈ ({x, y} : Set k) := by rw [hxy']; trivial
  have hc' : c ∈ ({x, y} : Set k) := by rw [hxy']; trivial
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 hc'
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases hc' with h | h <;>
    first
      | exact absurd (h1.trans h0.symm) one_ne_zero
      | exact absurd (h.trans h0.symm) hc
      | exact h.trans h1.symm

theorem natCast_eq_one_of_odd_char_two (k : Type*) [Field k] [CharP k 2] {n : ℕ} (hn : Odd n) :
    (n : k) = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  push_cast
  rw [h2]
  simp

end CFSG.QuasithinUnique.Setup.Offender
