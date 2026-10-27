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
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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
public import CFSG.LocalAnalysis.GLTheoremB.S7DecideK

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open Equiv Equiv.Perm

namespace S7

abbrev S : Type := Perm (Fin 7)

@[expose] def a : S := c[0, 1, 2]

@[expose] def b : S := c[3, 4, 5]

@[expose] def x : S := c[3, 4] * c[5, 6]

@[expose] def y : S := c[3, 5] * c[4, 6]

@[expose] def u : S := c[0, 1] * c[2, 6]

@[expose] def w : S := c[0, 2] * c[1, 6]

theorem a_mul_b : a * b = b * a := by decide
theorem a_pow_three : a ^ 3 = 1 := by decide
theorem b_pow_three : b ^ 3 = 1 := by decide
theorem x_mul_y : x * y = y * x := by decide
theorem x_mul_x : x * x = 1 := by decide
theorem y_mul_y : y * y = 1 := by decide
theorem u_mul_w : u * w = w * u := by decide
theorem u_mul_u : u * u = 1 := by decide
theorem w_mul_w : w * w = 1 := by decide
theorem a_mul_x : a * x = x * a := by decide
theorem a_mul_y : a * y = y * a := by decide
theorem b_mul_u : b * u = u * b := by decide
theorem b_mul_w : b * w = w * b := by decide

theorem x_mem : x ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem y_mem : y ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem u_mem : u ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem w_mem : w ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem threeCycle : ((x * u) ^ 2).IsThreeCycle := by
  have h : (x * u) ^ 2 = swap (2 : Fin 7) 5 * swap (2 : Fin 7) 6 := by decide
  rw [h]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem b_conj_x : b * x * b⁻¹ = x ∨ b * x * b⁻¹ = y ∨ b * x * b⁻¹ = x * y := by decide
theorem b_conj_y : b * y * b⁻¹ = x ∨ b * y * b⁻¹ = y ∨ b * y * b⁻¹ = x * y := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem conj_facts : ∀ c : S,
    (c * a = a * c →
      (c * x * c⁻¹ = x ∨ c * x * c⁻¹ = y ∨ c * x * c⁻¹ = x * y) ∧
      (c * y * c⁻¹ = x ∨ c * y * c⁻¹ = y ∨ c * y * c⁻¹ = x * y)) ∧
    (c * b = b * c →
      (c * u * c⁻¹ = u ∨ c * u * c⁻¹ = w ∨ c * u * c⁻¹ = u * w) ∧
      (c * w * c⁻¹ = u ∨ c * w * c⁻¹ = w ∨ c * w * c⁻¹ = u * w)) :=
  S7DecideK.conj_facts_K a b x y u w (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem conj_x_of_comm_a {c : S} (h : c * a = a * c) :
    c * x * c⁻¹ = x ∨ c * x * c⁻¹ = y ∨ c * x * c⁻¹ = x * y := ((conj_facts c).1 h).1

theorem conj_y_of_comm_a {c : S} (h : c * a = a * c) :
    c * y * c⁻¹ = x ∨ c * y * c⁻¹ = y ∨ c * y * c⁻¹ = x * y := ((conj_facts c).1 h).2

theorem conj_u_of_comm_b {c : S} (h : c * b = b * c) :
    c * u * c⁻¹ = u ∨ c * u * c⁻¹ = w ∨ c * u * c⁻¹ = u * w := ((conj_facts c).2 h).1

theorem conj_w_of_comm_b {c : S} (h : c * b = b * c) :
    c * w * c⁻¹ = u ∨ c * w * c⁻¹ = w ∨ c * w * c⁻¹ = u * w := ((conj_facts c).2 h).2

end S7

end CFSG.LocalAnalysis.GLTheoremB
