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

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi.Lift

open scoped commutatorElement

variable {Y : Type*} [Group Y]

@[expose] def Act (Lb : Subgroup Y) (y p : Y) : Prop :=
  ∀ l ∈ Lb, y * l * y⁻¹ = p * l * p⁻¹

@[expose] def ZL (Lb : Subgroup Y) : Subgroup Y := Lb ⊓ Subgroup.centralizer (Lb : Set Y)

theorem mem_ZL {Lb : Subgroup Y} {z : Y} : z ∈ ZL Lb ↔ z ∈ Lb ∧ ∀ m ∈ Lb, m * z = z * m := by
  simp [ZL, Subgroup.mem_centralizer_iff]

variable {Lb : Subgroup Y} {y y' p p' q : Y}

theorem act_one : Act Lb 1 1 := fun l _ => by simp

theorem act_mul (hp' : p' ∈ Lb) (h : Act Lb y p) (h' : Act Lb y' p') : Act Lb (y * y') (p * p') := by
  intro l hl
  have h1 := h' l hl
  have h2 := h (p' * l * p'⁻¹) (Lb.mul_mem (Lb.mul_mem hp' hl) (Lb.inv_mem hp'))
  calc y * y' * l * (y * y')⁻¹ = y * (y' * l * y'⁻¹) * y⁻¹ := by group
    _ = p * p' * l * (p * p')⁻¹ := by rw [h1, h2]; group

theorem act_inv (hp : p ∈ Lb) (h : Act Lb y p) : Act Lb y⁻¹ p⁻¹ := by
  intro l hl
  have h1 := h (p⁻¹ * l * p) (Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hp) hl) hp)
  have h2 : y * (p⁻¹ * l * p) * y⁻¹ = l := by rw [h1]; group
  calc y⁻¹ * l * y⁻¹⁻¹ = y⁻¹ * (y * (p⁻¹ * l * p) * y⁻¹) * y := by rw [h2]; group
    _ = p⁻¹ * l * p⁻¹⁻¹ := by group

theorem act_pow (hp : p ∈ Lb) (h : Act Lb y p) (n : ℕ) : Act Lb (y ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using act_one
  | succ n ih => rw [pow_succ, pow_succ]; exact act_mul hp ih h

theorem act_comm (hp : p ∈ Lb) (hp' : p' ∈ Lb) (h : Act Lb y p) (h' : Act Lb y p') :
    p⁻¹ * p' ∈ ZL Lb := by
  refine mem_ZL.2 ⟨Lb.mul_mem (Lb.inv_mem hp) hp', fun m hm => ?_⟩
  have := (h m hm).symm.trans (h' m hm)
  calc m * (p⁻¹ * p') = p⁻¹ * (p * m * p⁻¹) * p' := by group
    _ = p⁻¹ * (p' * m * p'⁻¹) * p' := by rw [this]
    _ = p⁻¹ * p' * m := by group

theorem act_of_central (hz : p⁻¹ * p' ∈ ZL Lb) (h : Act Lb y p) : Act Lb y p' := by
  intro l hl
  obtain ⟨-, hzc⟩ := mem_ZL.1 hz
  have hc := hzc l hl
  have hp'' : p' = p * (p⁻¹ * p') := by group
  have h1 : (p⁻¹ * p') * l * (p⁻¹ * p')⁻¹ = l := by rw [← hc]; group
  rw [h l hl]
  generalize p⁻¹ * p' = c at hp'' h1
  subst hp''
  calc p * l * p⁻¹ = p * (c * l * c⁻¹) * p⁻¹ := by rw [h1]
    _ = _ := by group

theorem mem_ZL_of_act_one (hq : q ∈ Lb) (h : Act Lb 1 q) : q ∈ ZL Lb := by
  refine mem_ZL.2 ⟨hq, fun m hm => ?_⟩
  have := h m hm
  simp at this
  calc m * q = q * m * q⁻¹ * q := by rw [← this]
    _ = q * m := by group

theorem act_one_of_mem_ZL (hq : q ∈ ZL Lb) : Act Lb 1 q := by
  obtain ⟨-, hc⟩ := mem_ZL.1 hq
  intro l hl
  rw [← hc l hl]; group

end CFSG.HardMathSupport.Curtis.UnitaryLevi.Lift
