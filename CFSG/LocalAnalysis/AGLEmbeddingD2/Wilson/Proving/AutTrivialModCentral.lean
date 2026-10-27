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

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem aut_trivial_of_mod_central {P : Type*} [Group P]
    (hperf : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) = ⊤)
    (Z : Subgroup P) (hZ : ∀ z ∈ Z, z ∈ Subgroup.center P) (α : MulAut P)
    (hα : ∀ x : P, α x * x⁻¹ ∈ Z) : ∀ x : P, α x = x := by
  set g : P → P := fun x => α x * x⁻¹ with hg
  have hgc : ∀ x, g x ∈ Subgroup.center P := fun x => hZ _ (hα x)
  have hg1 : g 1 = 1 := by simp [hg]
  have hmul : ∀ x y, g (x * y) = g y * g x := by
    intro x y
    have hc : α x * (α y * y⁻¹) = (α y * y⁻¹) * α x :=
      (Subgroup.mem_center_iff.mp (hgc y)) (α x)
    show α (x * y) * (x * y)⁻¹ = (α y * y⁻¹) * (α x * x⁻¹)
    rw [map_mul, mul_inv_rev]
    calc α x * α y * (y⁻¹ * x⁻¹) = α x * (α y * y⁻¹) * x⁻¹ := by simp only [mul_assoc]
      _ = (α y * y⁻¹) * α x * x⁻¹ := by rw [hc]
      _ = (α y * y⁻¹) * (α x * x⁻¹) := by simp only [mul_assoc]
  have hcomm : ∀ x y, g x * g y = g y * g x := fun x y =>
    (Subgroup.mem_center_iff.mp (hgc y)) (g x)
  have hinv : ∀ x, g x⁻¹ * g x = 1 := by
    intro x
    have h := hmul x x⁻¹
    rw [mul_inv_cancel, hg1] at h
    exact h.symm
  let K : Subgroup P :=
    { carrier := {x | g x = 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : g a = 1 := ha
        have hb' : g b = 1 := hb
        show g (a * b) = 1
        rw [hmul, ha', hb', one_mul]
      one_mem' := hg1
      inv_mem' := fun {a} ha => by
        have ha' : g a = 1 := ha
        show g a⁻¹ = 1
        have h := hinv a
        rw [ha', mul_one] at h
        exact h }
  have hcomm_le : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) ≤ K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    show g (a * b * a⁻¹ * b⁻¹) = 1
    rw [hmul (a * b * a⁻¹) b⁻¹, hmul (a * b) a⁻¹, hmul a b,
      hcomm b a, ← mul_assoc (g a⁻¹) (g a) (g b), hinv a, one_mul, hinv b]
  have hK : (⊤ : Subgroup P) ≤ K := hperf ▸ hcomm_le
  intro x
  have h : g x = 1 := hK (Subgroup.mem_top x)
  exact mul_inv_eq_one.mp h

end CFSG.AGLEmbeddingD2.Wilson.Proving
