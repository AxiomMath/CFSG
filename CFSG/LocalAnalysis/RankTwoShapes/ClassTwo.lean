module

public import CFSG.LocalAnalysis.RankTwoShapes.FixedPointFreeThree
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

namespace CFSG.RankTwoShapes

universe u

variable {Q : Type u} [Group Q]

@[expose] def CentralCommutators (Q : Type u) [Group Q] : Prop :=
  ∀ a b g : Q, Commute (rcomm a b) g

theorem centralCommutators_of_fpfThree [Finite Q] (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ x : Q, α x = x → x = 1) : CentralCommutators Q :=
  fpfThree_rcomm_central α hα hfpf

variable (hcen : CentralCommutators Q)
include hcen

theorem rcomm_mul_left_central (a b s : Q) : rcomm (a * b) s = rcomm a s * rcomm b s := by
  have h := (hcen a s b).eq
  calc rcomm (a * b) s = b⁻¹ * (rcomm a s * b) * rcomm b s := by simp only [rcomm]; group
    _ = b⁻¹ * (b * rcomm a s) * rcomm b s := by rw [h]
    _ = rcomm a s * rcomm b s := by group

theorem rcomm_mul_right_central (a s t : Q) : rcomm a (s * t) = rcomm a s * rcomm a t := by
  have h := (hcen a s t).eq
  calc rcomm a (s * t) = rcomm a t * (t⁻¹ * rcomm a s * t) := by simp only [rcomm]; group
    _ = rcomm a t * (t⁻¹ * (t * rcomm a s)) := by rw [mul_assoc t⁻¹, h]
    _ = rcomm a s * rcomm a t := by
      rw [inv_mul_cancel_left]; exact (hcen a s (rcomm a t)).eq.symm

omit hcen in
theorem rcomm_one_left (s : Q) : rcomm (1 : Q) s = 1 := by simp [rcomm]

omit hcen in
theorem rcomm_one_right (a : Q) : rcomm a (1 : Q) = 1 := by simp [rcomm]

theorem rcomm_inv_left_central (a s : Q) : rcomm a⁻¹ s = (rcomm a s)⁻¹ := by
  have h := rcomm_mul_left_central hcen a⁻¹ a s
  rw [inv_mul_cancel, rcomm_one_left] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem rcomm_inv_right_central (a s : Q) : rcomm a s⁻¹ = (rcomm a s)⁻¹ := by
  have h := rcomm_mul_right_central hcen a s⁻¹ s
  rw [inv_mul_cancel, rcomm_one_right] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem rcomm_pow_left_central (a s : Q) (n : ℕ) : rcomm (a ^ n) s = rcomm a s ^ n := by
  induction n with
  | zero => simp [rcomm]
  | succ n ih => rw [pow_succ, rcomm_mul_left_central hcen, ih, pow_succ]

theorem rcomm_pow_right_central (a s : Q) (n : ℕ) : rcomm a (s ^ n) = rcomm a s ^ n := by
  induction n with
  | zero => simp [rcomm]
  | succ n ih => rw [pow_succ, rcomm_mul_right_central hcen, ih, pow_succ]

omit hcen in
theorem mul_eq_mul_rcomm (a g : Q) : a * g = g * a * rcomm a g := by
  simp only [rcomm]; group

theorem mul_pow_central (g a : Q) (n : ℕ) :
    (g * a) ^ n = g ^ n * a ^ n * rcomm a g ^ (n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set c := rcomm a g with hcdef
    have hc : ∀ k : ℕ, Commute (c ^ k) g := fun k => (hcen a g g).pow_left k
    have hca : ∀ k : ℕ, Commute (c ^ k) a := fun k => (hcen a g a).pow_left k
    have hsw : a ^ n * g = g * a ^ n * c ^ n := by
      rw [mul_eq_mul_rcomm (a ^ n) g, rcomm_pow_left_central hcen]
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_succ, ih]
    calc g ^ n * a ^ n * c ^ (n.choose 2) * (g * a)
        = g ^ n * a ^ n * (c ^ (n.choose 2) * g) * a := by simp only [mul_assoc]
      _ = g ^ n * (a ^ n * g) * c ^ (n.choose 2) * a := by
          rw [(hc _).eq]; simp only [mul_assoc]
      _ = g ^ n * (g * a ^ n * c ^ n) * c ^ (n.choose 2) * a := by rw [hsw]
      _ = g ^ (n + 1) * a ^ n * (c ^ n * c ^ (n.choose 2) * a) := by
          rw [pow_succ]; simp only [mul_assoc]
      _ = g ^ (n + 1) * a ^ n * (a * (c ^ n * c ^ (n.choose 2))) := by
          rw [((hca n).mul_left (hca _)).eq]
      _ = g ^ (n + 1) * a ^ (n + 1) * c ^ (n + n.choose 2) := by
          rw [pow_succ a n, pow_add c n]; simp only [mul_assoc]

end CFSG.RankTwoShapes
