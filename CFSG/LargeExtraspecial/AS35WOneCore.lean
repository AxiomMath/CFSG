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

namespace CFSG.LargeExtraspecial

namespace AS35W

variable {X : Type} [Group X] {z : X} {R : Subgroup X}

structure QuatLike (z : X) (R : Subgroup X) : Prop where
  z_mul_z : z * z = 1
  z_ne_one : z ≠ 1
  z_mem : z ∈ R
  comm_z : ∀ r ∈ R, r * z = z * r
  cases : ∀ r ∈ R, r = 1 ∨ r = z ∨ r ^ 2 = z

namespace QuatLike

variable (h : QuatLike z R)
include h

theorem inv_eq {a : X} (ha : a ^ 2 = z) : a⁻¹ = a * z := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← sq, ha, h.z_mul_z]

theorem eq_of_commute {a b : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hab : a * b = b * a) : b = a ∨ b = a * z := by
  have hsq : (a * b) ^ 2 = 1 := by
    rw [sq, show a * b * (a * b) = a * a * (b * b) by
      rw [mul_assoc, ← mul_assoc b a b, ← hab]; group, ← sq, ← sq, ha, hb, h.z_mul_z]
  rcases h.cases _ (R.mul_mem haR hbR) with h1 | h1 | h1
  · right
    rw [← h.inv_eq ha]
    exact (eq_inv_of_mul_eq_one_right h1)
  · left
    have : b = a⁻¹ * z := by rw [← h1]; group
    rw [this, h.inv_eq ha, mul_assoc, h.z_mul_z, mul_one]
  · exact absurd (h1.symm.trans hsq) h.z_ne_one

theorem mul_comm_eq {a b : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hne : b ≠ a ∧ b ≠ a * z) : b * a = a * b * z := by
  have hnc : a * b ≠ b * a := fun hc => by
    rcases h.eq_of_commute haR hbR ha hb hc with h1 | h1
    · exact hne.1 h1
    · exact hne.2 h1
  have hab1 : a * b ≠ 1 := fun h1 => hnc (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, mul_inv_cancel, inv_mul_cancel])
  have habz : a * b ≠ z := fun h1 => hnc (by
    have hb' : b = a⁻¹ * z := by rw [← h1]; group
    rw [hb']
    calc a * (a⁻¹ * z) = z := by group
      _ = a⁻¹ * (a * z) := by group
      _ = a⁻¹ * z * a := by rw [h.comm_z a haR, mul_assoc])
  rcases h.cases _ (R.mul_mem haR hbR) with h1 | h1 | h1
  · exact absurd h1 hab1
  · exact absurd h1 habz
  · have hz' : a * b * a * b = z := by rw [← h1, sq]; group
    calc b * a = a⁻¹ * (a * b * a * b) * b⁻¹ := by group
      _ = a * z * z * (b * z) := by rw [hz', h.inv_eq ha, h.inv_eq hb]
      _ = a * (z * z) * (b * z) := by group
      _ = a * b * z := by rw [h.z_mul_z, mul_one, mul_assoc]

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_mul_z

theorem mul_ne_one {a b : X} (ha : a ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z) : a * b ≠ 1 := fun h1 => by
  have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
  exact hne.2 (by rw [this, h.inv_eq ha])

theorem mul_ne_z {a b : X} (ha : a ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z) : a * b ≠ z :=
    fun h1 => by
  have : b = a⁻¹ * z := by rw [← h1]; group
  exact hne.1 (by rw [this, h.inv_eq ha, mul_assoc, h.z_mul_z, mul_one])

theorem sq_mul {a b : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z)
    (hne : b ≠ a ∧ b ≠ a * z) : (a * b) ^ 2 = z := by
  rcases h.cases _ (R.mul_mem haR hbR) with h1 | h1 | h1
  · exact absurd h1 (h.mul_ne_one ha hne)
  · exact absurd h1 (h.mul_ne_z ha hne)
  · exact h1

theorem mem_eight {a b r : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hne : b ≠ a ∧ b ≠ a * z) (hr : r ∈ R) :
    r = 1 ∨ r = z ∨ r = a ∨ r = a * z ∨ r = b ∨ r = b * z ∨ r = a * b ∨ r = a * b * z := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨h1, hz, ha1, ha2, hb1, hb2, hab1, hab2⟩ := hc
  have hr2 : r ^ 2 = z := by
    rcases h.cases r hr with h' | h' | h'
    · exact absurd h' h1
    · exact absurd h' hz
    · exact h'
  have hra : r * a = a * r * z := h.mul_comm_eq haR hr ha hr2 ⟨ha1, ha2⟩
  have hrb : r * b = b * r * z := h.mul_comm_eq hbR hr hb hr2 ⟨hb1, hb2⟩
  have hab2' : (a * b) ^ 2 = z := h.sq_mul haR hbR ha hne
  have hcomm : a * b * r = r * (a * b) := by
    have e1 : b * r = r * b * z := by
      calc b * r = b * r * z * z := by rw [mul_assoc (b * r), h.z_mul_z, mul_one]
        _ = r * b * z := by rw [← hrb]
    have e2 : a * r = r * a * z := by
      calc a * r = a * r * z * z := by rw [mul_assoc (a * r), h.z_mul_z, mul_one]
        _ = r * a * z := by rw [← hra]
    calc a * b * r = a * (b * r) := by group
      _ = a * (r * b * z) := by rw [e1]
      _ = a * r * b * z := by group
      _ = r * a * z * b * z := by rw [e2]
      _ = r * a * (z * b) * z := by group
      _ = r * a * (b * z) * z := by rw [h.comm_z b hbR]
      _ = r * (a * b) * (z * z) := by group
      _ = r * (a * b) := by rw [h.z_mul_z, mul_one]
  rcases h.eq_of_commute (R.mul_mem haR hbR) hr hab2' hr2 hcomm with h' | h'
  · exact hab1 h'
  · exact hab2 h'

end QuatLike

end AS35W

end CFSG.LargeExtraspecial
