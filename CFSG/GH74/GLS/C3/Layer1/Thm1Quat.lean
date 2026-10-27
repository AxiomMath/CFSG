module

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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open QuaternionGroup Subgroup
open scoped commutatorElement

section Comm

variable {n : ℕ}

theorem q_inv_a (s : ZMod (2 * n)) : (a s : QuaternionGroup n)⁻¹ = a (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [a_mul_a, add_neg_cancel, one_def]

theorem q_nn : ((n : ZMod (2 * n)) + n) = 0 := by
  have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
  push_cast at this
  rw [← this]
  ring

theorem q_inv_xa (s : ZMod (2 * n)) :
    (xa s : QuaternionGroup n)⁻¹ = xa ((n : ZMod (2 * n)) + s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [xa_mul_xa, one_def]
  congr 1
  rw [← add_assoc, q_nn]
  ring

theorem q_comm_a_xa (s j : ZMod (2 * n)) : ⁅(a s : QuaternionGroup n), xa j⁆ = a (2 * s) := by
  rw [commutatorElement_def, q_inv_a, q_inv_xa, a_mul_xa, xa_mul_a, xa_mul_xa]
  congr 1
  have := q_nn (n := n)
  linear_combination this

theorem q_comm_a_a (s t : ZMod (2 * n)) : ⁅(a s : QuaternionGroup n), a t⁆ = 1 := by
  rw [commutatorElement_def, q_inv_a, q_inv_a, a_mul_a, a_mul_a, a_mul_a, one_def]
  congr 1
  ring

theorem q_comm_xa_a (i s : ZMod (2 * n)) :
    ⁅(xa i : QuaternionGroup n), a s⁆ = a (-(2 * s)) := by
  rw [commutatorElement_def, q_inv_a, q_inv_xa, xa_mul_a, xa_mul_xa, a_mul_a]
  congr 1
  have := q_nn (n := n)
  linear_combination this

theorem q_comm_xa_xa (i j : ZMod (2 * n)) :
    ⁅(xa i : QuaternionGroup n), xa j⁆ = a (2 * j - 2 * i) := by
  rw [commutatorElement_def, q_inv_xa, q_inv_xa, xa_mul_xa, a_mul_xa, xa_mul_xa]
  congr 1
  have := q_nn (n := n)
  linear_combination this

end Comm

def rotSub (n k : ℕ) : Subgroup (QuaternionGroup n) where
  carrier := {g | ∃ s m : ZMod (2 * n), g = a s ∧ s = 2 ^ k * m}
  one_mem' := ⟨0, 0, one_def, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨s, m, rfl, hs⟩ ⟨t, m', rfl, ht⟩
    exact ⟨s + t, m + m', a_mul_a s t, by rw [hs, ht]; ring⟩
  inv_mem' := by
    rintro _ ⟨s, m, rfl, hs⟩
    exact ⟨-s, -m, q_inv_a s, by rw [hs]; ring⟩

theorem lcs_le (n : ℕ) (k : ℕ) :
    (⊤ : Subgroup (QuaternionGroup n)).lowerCentralSeries (k + 1) ≤ rotSub n (k + 1) := by
  induction k with
  | zero =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero, Subgroup.commutator_le]
    intro g _ h _
    cases g with
    | a s =>
      cases h with
      | a t => exact ⟨0, 0, by rw [q_comm_a_a, one_def], by simp⟩
      | xa j => exact ⟨2 * s, s, q_comm_a_xa s j, by ring⟩
    | xa i =>
      cases h with
      | a s => exact ⟨-(2 * s), -s, q_comm_xa_a i s, by ring⟩
      | xa j => exact ⟨2 * j - 2 * i, j - i, q_comm_xa_xa i j, by ring⟩
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro g hg h _
    obtain ⟨s, m, rfl, hs⟩ := ih hg
    cases h with
    | a t => exact ⟨0, 0, by rw [q_comm_a_a, one_def], by simp⟩
    | xa j => exact ⟨2 * s, m, q_comm_a_xa s j, by rw [hs]; ring⟩

theorem a_mem_lcs (n : ℕ) (k : ℕ) :
    (a ((2 : ZMod (2 * n)) ^ (k + 1)) : QuaternionGroup n) ∈
      (⊤ : Subgroup (QuaternionGroup n)).lowerCentralSeries (k + 1) := by
  induction k with
  | zero =>
    have h := Subgroup.commutator_mem_commutator (mem_top (a 1 : QuaternionGroup n))
      (mem_top (xa 0 : QuaternionGroup n))
    rw [q_comm_a_xa] at h
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    simpa using h
  | succ k ih =>
    have h := Subgroup.commutator_mem_commutator ih (mem_top (xa 0 : QuaternionGroup n))
    rw [q_comm_a_xa] at h
    rw [Subgroup.lowerCentralSeries_succ _ (k + 1)]
    convert h using 2
    ring

theorem quaternionGroup_class (e : ℕ) (he : 1 ≤ e) :
    Group.nilpotencyClass (QuaternionGroup (2 ^ e)) = e + 1 ∧
      Nat.card (QuaternionGroup (2 ^ e)) = 2 ^ (e + 2) := by
  have hcard : Nat.card (QuaternionGroup (2 ^ e)) = 2 ^ (e + 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hp : IsPGroup 2 (QuaternionGroup (2 ^ e)) := IsPGroup.of_card hcard
  have : Group.IsNilpotent (QuaternionGroup (2 ^ e)) := hp.isNilpotent
  have hzero : (2 : ZMod (2 * 2 ^ e)) ^ (e + 1) = 0 := by
    have h1 : ((2 ^ (e + 1) : ℕ) : ZMod (2 * 2 ^ e)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨1, by ring⟩
    simpa using h1
  have hne : (2 : ZMod (2 * 2 ^ e)) ^ e ≠ 0 := by
    intro h
    have h1 : ((2 ^ e : ℕ) : ZMod (2 * 2 ^ e)) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by positivity) h1
    have : 0 < 2 ^ e := by positivity
    omega
  have hbot : (⊤ : Subgroup (QuaternionGroup (2 ^ e))).lowerCentralSeries (e + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨s, m, rfl, hs⟩ := lcs_le (2 ^ e) e hg
    rw [Subgroup.mem_bot, one_def]
    congr 1
    rw [hs, hzero, zero_mul]
  have hnb : (⊤ : Subgroup (QuaternionGroup (2 ^ e))).lowerCentralSeries e ≠ ⊥ := by
    intro hb
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have := a_mem_lcs (2 ^ (e' + 1)) e'
    rw [hb, Subgroup.mem_bot, one_def] at this
    have h1 := congrArg (fun g => match g with | a s => s | xa s => s) this
    exact hne h1
  refine ⟨le_antisymm ?_ ?_, hcard⟩
  · exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.1 hbot
  · by_contra hlt
    push Not at hlt
    exact hnb (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.2 (by omega))

end CFSG.GH74.GLS.C3.Layer1.Thm1
