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

namespace CFSG.GH74.Uniqueness

open Subgroup

section Dihedral

variable {X : Type*} [Group X]

theorem semiconj_mul_of_sq {s t : X} (hs : s * s = 1) (ht : t * t = 1) :
    SemiconjBy s (s * t) (s * t)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  change s * (s * t) = (s * t)⁻¹ * s
  rw [mul_inv_rev, hs', ht', ← mul_assoc, hs, one_mul, mul_assoc, hs, mul_one]

theorem semiconj_mul_of_sq' {s t : X} (hs : s * s = 1) (ht : t * t = 1) :
    SemiconjBy t (s * t) (s * t)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  change t * (s * t) = (s * t)⁻¹ * t
  rw [mul_inv_rev, hs', ht']
  exact (mul_assoc t s t).symm

theorem exists_mem_closure_conj_of_odd {s t : X} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) : ∃ x ∈ Subgroup.closure ({s, t} : Set X), x⁻¹ * t * x = s := by
  obtain ⟨k, hk⟩ := hodd
  set w := s * t with hw
  have hwk : w ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one w
  have hws : ∀ n : ℕ, t * w ^ n = (w ^ n)⁻¹ * t := fun n => by
    have := (semiconj_mul_of_sq' hs ht).pow_right n
    rw [SemiconjBy] at this
    rw [inv_pow] at this
    exact this
  have hmem : w ∈ Subgroup.closure ({s, t} : Set X) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨w ^ k, Subgroup.pow_mem _ hmem k, ?_⟩
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hwinv : w⁻¹ = t * s := by
    rw [hw, mul_inv_rev, hs', inv_eq_of_mul_eq_one_right ht]
  calc (w ^ k)⁻¹ * t * w ^ k = (w ^ k)⁻¹ * (t * w ^ k) := by rw [mul_assoc]
    _ = (w ^ k)⁻¹ * ((w ^ k)⁻¹ * t) := by rw [hws k]
    _ = (w ^ (k + k))⁻¹ * t := by rw [← mul_assoc, ← mul_inv_rev, ← pow_add]
    _ = w * t := by
        have h2 : w ^ (k + k) * w = 1 := by
          rw [← pow_succ, show k + k + 1 = 2 * k + 1 by ring, hwk]
        rw [inv_eq_of_mul_eq_one_right h2]
    _ = s := by rw [hw, mul_assoc, ht, mul_one]


theorem exists_involution_conj_of_odd {s t : X} (hs : s * s = 1) (ht : t * t = 1)
    (hodd : Odd (orderOf (s * t))) :
    ∃ x y : X, x ∈ Subgroup.closure ({s, t} : Set X) ∧ y ∈ Subgroup.closure ({s, t} : Set X) ∧
      x * x = 1 ∧ y⁻¹ * t * y = x ∧ x⁻¹ * t * x = s := by
  obtain ⟨m, hm⟩ := hodd
  set w := s * t with hw
  have hwn : w ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one w
  have hws : ∀ n : ℕ, t * w ^ n = (w ^ n)⁻¹ * t := fun n => by
    have := (semiconj_mul_of_sq' hs ht).pow_right n
    rw [SemiconjBy] at this
    rw [inv_pow] at this
    exact this
  have hmem : w ∈ Subgroup.closure ({s, t} : Set X) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have htmem : t ∈ Subgroup.closure ({s, t} : Set X) := Subgroup.subset_closure (by simp)
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hwinv : w⁻¹ = t * s := by
    rw [hw, mul_inv_rev, hs', inv_eq_of_mul_eq_one_right ht]
  have hxx : (t * w ^ m) * (t * w ^ m) = 1 := by
    calc (t * w ^ m) * (t * w ^ m) = (t * w ^ m * t) * w ^ m := by group
      _ = (w ^ m)⁻¹ * t * t * w ^ m := by rw [hws m]
      _ = 1 := by rw [mul_assoc ((w ^ m)⁻¹) t t, ht, mul_one, inv_mul_cancel]
  have hx2 : w ^ m * w ^ m = w⁻¹ := by
    rw [← pow_add]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show m + m + 1 = 2 * m + 1 by ring, hwn]
  refine ⟨t * w ^ m, w ^ (m * (m + 1)), mul_mem htmem (Subgroup.pow_mem _ hmem m),
    Subgroup.pow_mem _ hmem _, hxx, ?_, ?_⟩
  ·
    have h2j : w ^ (m * (m + 1)) * w ^ (m * (m + 1)) = w ^ m := by
      rw [← pow_add, show m * (m + 1) + m * (m + 1) = (2 * m + 1) * m + m by ring, pow_add,
        pow_mul, hwn, one_pow, one_mul]
    calc (w ^ (m * (m + 1)))⁻¹ * t * w ^ (m * (m + 1))
        = ((w ^ (m * (m + 1)))⁻¹ * t) * w ^ (m * (m + 1)) := rfl
      _ = (t * w ^ (m * (m + 1))) * w ^ (m * (m + 1)) := by rw [← hws]
      _ = t * (w ^ (m * (m + 1)) * w ^ (m * (m + 1))) := by rw [mul_assoc]
      _ = t * w ^ m := by rw [h2j]
  ·
    have hxinv : (t * w ^ m)⁻¹ = t * w ^ m := inv_eq_of_mul_eq_one_right hxx
    rw [hxinv]
    calc t * w ^ m * t * (t * w ^ m) = t * (w ^ m * (t * t) * w ^ m) := by group
      _ = t * (w ^ m * w ^ m) := by rw [ht, mul_one]
      _ = t * w⁻¹ := by rw [hx2]
      _ = s := by rw [hwinv, ← mul_assoc, ht, one_mul]

theorem dihedral_even {s t : X} (hs : s * s = 1) (ht : t * t = 1) {m : ℕ} (hm : 0 < m)
    (hord : orderOf (s * t) = 2 * m) :
    (s * t) ^ m * (s * t) ^ m = 1 ∧ (s * t) ^ m ≠ 1 ∧
      s * (s * t) ^ m = (s * t) ^ m * s ∧ t * (s * t) ^ m = (s * t) ^ m * t ∧
      ∃ x ∈ Subgroup.closure ({s, t} : Set X),
        x⁻¹ * s * x = s * (s * t) ^ m ∨ x⁻¹ * t * x = s * (s * t) ^ m := by
  set w := s * t with hw
  have hw2 : w ^ (2 * m) = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
  have hv2 : w ^ m * w ^ m = 1 := by rw [← pow_add, ← two_mul]; exact hw2
  have hvinv : (w ^ m)⁻¹ = w ^ m := inv_eq_of_mul_eq_one_right hv2
  have hv1 : w ^ m ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    have := Nat.le_of_dvd hm this
    omega
  have hsw : ∀ n : ℕ, s * w ^ n = (w ^ n)⁻¹ * s := fun n => by
    have := (semiconj_mul_of_sq hs ht).pow_right n
    rw [SemiconjBy, inv_pow] at this
    exact this
  have htw : ∀ n : ℕ, t * w ^ n = (w ^ n)⁻¹ * t := fun n => by
    have := (semiconj_mul_of_sq' hs ht).pow_right n
    rw [SemiconjBy, inv_pow] at this
    exact this
  have hsv : s * w ^ m = w ^ m * s := by rw [hsw m, hvinv]
  have htv : t * w ^ m = w ^ m * t := by rw [htw m, hvinv]
  refine ⟨hv2, hv1, hsv, htv, ?_⟩
  have hmem : w ∈ Subgroup.closure ({s, t} : Set X) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hs_mem : s ∈ Subgroup.closure ({s, t} : Set X) := Subgroup.subset_closure (by simp)
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  ·
    refine ⟨w ^ j, Subgroup.pow_mem _ hmem j, Or.inl ?_⟩
    calc (w ^ j)⁻¹ * s * w ^ j = (w ^ j)⁻¹ * (s * w ^ j) := by rw [mul_assoc]
      _ = (w ^ j)⁻¹ * ((w ^ j)⁻¹ * s) := by rw [hsw j]
      _ = (w ^ (j + j))⁻¹ * s := by rw [← mul_assoc, ← mul_inv_rev, ← pow_add]
      _ = (w ^ m)⁻¹ * s := by rw [hj, two_mul]
      _ = w ^ m * s := by rw [hvinv]
      _ = s * w ^ m := hsv.symm
  ·
    refine ⟨(w ^ (j + 1))⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hmem _), Or.inr ?_⟩
    have hti : ∀ n : ℕ, t * (w ^ n)⁻¹ = w ^ n * t := fun n => by
      have h := htw n
      have : (w ^ n)⁻¹ * (t * (w ^ n)⁻¹) = (w ^ n)⁻¹ * (w ^ n * t) := by
        calc (w ^ n)⁻¹ * (t * (w ^ n)⁻¹) = ((w ^ n)⁻¹ * t) * (w ^ n)⁻¹ := by rw [mul_assoc]
          _ = (t * w ^ n) * (w ^ n)⁻¹ := by rw [h]
          _ = t := by rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = (w ^ n)⁻¹ * (w ^ n * t) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact mul_left_cancel this
    have hwt : w * t = s := by rw [hw, mul_assoc, ht, mul_one]
    calc ((w ^ (j + 1))⁻¹)⁻¹ * t * (w ^ (j + 1))⁻¹
        = w ^ (j + 1) * (t * (w ^ (j + 1))⁻¹) := by rw [inv_inv, mul_assoc]
      _ = w ^ (j + 1) * (w ^ (j + 1) * t) := by rw [hti]
      _ = w ^ (j + 1 + (j + 1)) * t := by rw [← mul_assoc, ← pow_add]
      _ = w ^ (2 * j + 1) * (w * t) := by rw [show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring,
            pow_succ, mul_assoc]
      _ = w ^ m * s := by rw [hwt, hj]
      _ = s * w ^ m := hsv.symm

end Dihedral

end CFSG.GH74.Uniqueness
