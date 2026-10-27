module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.GroupAction.ConjAct
public meta import Mathlib
public import Certificates.Certificate5017
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

namespace CFSG.GH74.E2

open Subgroup

section Q8AutFacts

private def IsInvAut (σ : MulAut (QuaternionGroup 2)) : Prop := ∀ y, σ (σ y) = y

private def IsInnerAut (σ : MulAut (QuaternionGroup 2)) : Prop :=
  ∃ q : QuaternionGroup 2, ∀ y, σ y = q * y * q⁻¹

private def IsCubeAut (γ : MulAut (QuaternionGroup 2)) : Prop := ∀ y, γ (γ (γ y)) = y

private def MovesPt (γ : MulAut (QuaternionGroup 2)) : Prop := ∃ y, γ y ≠ y

private def CommAut (σ γ : MulAut (QuaternionGroup 2)) : Prop := ∀ y, σ (γ y) = γ (σ y)

private instance : DecidablePred IsInvAut := fun σ => by unfold IsInvAut; infer_instance
private instance : DecidablePred IsInnerAut := fun σ => by unfold IsInnerAut; infer_instance
private instance : DecidablePred IsCubeAut := fun σ => by unfold IsCubeAut; infer_instance
private instance : DecidablePred MovesPt := fun σ => by unfold MovesPt; infer_instance
private instance : DecidableRel CommAut := fun σ γ => by unfold CommAut; infer_instance

private theorem q8aut_fixed :
    ∀ σ : MulAut (QuaternionGroup 2), IsInvAut σ → ¬ IsInnerAut σ →
    ∀ x, σ x = x → x = 1 ∨ x = QuaternionGroup.a 2 :=
  Certificates.certificate5017.1

private theorem q8aut_no_comm :
    ∀ σ γ : MulAut (QuaternionGroup 2), IsInvAut σ → ¬ IsInnerAut σ →
    IsCubeAut γ → MovesPt γ → ¬ CommAut σ γ :=
  Certificates.certificate5017.2.1

private theorem q8aut_twisted :
    ∀ σ : MulAut (QuaternionGroup 2), IsInvAut σ → ¬ IsInnerAut σ →
    ∀ q, q * σ q = 1 → ∃ d, q = d * (σ d)⁻¹ :=
  Certificates.certificate5017.2.2

private theorem q8_sq_eq_one : ∀ x : QuaternionGroup 2, x * x = 1 →
    x = 1 ∨ x = QuaternionGroup.a 2 := by decide

end Q8AutFacts

section Transport

variable {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal] (e : ↥Q ≃* QuaternionGroup 2)

private def uAut (u : X) : MulAut (QuaternionGroup 2) :=
  MulAut.congr e (MulAut.conjNormal u)

private theorem uAut_apply (u : X) (x : QuaternionGroup 2) :
    ((e.symm (uAut Q e u x) : ↥Q) : X) = u * (e.symm x : X) * u⁻¹ := by
  simp [uAut, MulAut.congr_apply, MulAut.conjNormal_apply]

private theorem uAut_mul_apply (u v : X) (x : QuaternionGroup 2) :
    ((e.symm (uAut Q e u (uAut Q e v x)) : ↥Q) : X) = (u * v) * (e.symm x : X) * (u * v)⁻¹ := by
  rw [uAut_apply, uAut_apply]
  group

private theorem uAut_fix (u : X) (hu2 : u * u = 1) : IsInvAut (uAut Q e u) := by
  intro y
  apply e.symm.injective
  apply Subtype.ext
  rw [uAut_mul_apply, hu2]
  simp

private theorem uAut_not_inner (u : X)
    (hout : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹) :
    ¬ IsInnerAut (uAut Q e u) := by
  rintro ⟨q0, hq0⟩
  apply hout
  refine ⟨(e.symm q0 : X), (e.symm q0).2, fun y hy => ?_⟩
  have h1 := congrArg (fun z => ((e.symm z : ↥Q) : X)) (hq0 (e ⟨y, hy⟩))
  simp only [uAut_apply, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1

end Transport

theorem q8_fixed_pts
    {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    (e : ↥Q ≃* QuaternionGroup 2) {u : X} (hu2 : u * u = 1)
    (hout : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹) {t : X} (htQ : t ∈ Q)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∀ q ∈ Q, u * q * u⁻¹ = q → q = 1 ∨ q = t := by
  intro q hq hfix
  have hx : uAut Q e u (e ⟨q, hq⟩) = e ⟨q, hq⟩ := by
    apply e.symm.injective
    apply Subtype.ext
    rw [uAut_apply, MulEquiv.symm_apply_apply]
    exact hfix
  rcases q8aut_fixed (uAut Q e u) (uAut_fix Q e u hu2) (uAut_not_inner Q e u hout) _ hx with h | h
  · left
    have : (⟨q, hq⟩ : ↥Q) = 1 := by
      apply e.injective
      rw [h, map_one]
    exact congrArg Subtype.val this
  · right
    have ht : e ⟨t, htQ⟩ = QuaternionGroup.a 2 := by
      have h1 : e ⟨t, htQ⟩ * e ⟨t, htQ⟩ = 1 := by
        rw [← map_mul]
        have : (⟨t, htQ⟩ : ↥Q) * ⟨t, htQ⟩ = 1 := Subtype.ext ht2
        rw [this, map_one]
      rcases q8_sq_eq_one _ h1 with h2 | h2
      · exfalso
        apply ht1
        have : (⟨t, htQ⟩ : ↥Q) = 1 := by
          apply e.injective
          rw [h2, map_one]
        exact congrArg Subtype.val this
      · exact h2
    have : (⟨q, hq⟩ : ↥Q) = ⟨t, htQ⟩ := by
      apply e.injective
      rw [h, ht]
    exact congrArg Subtype.val this

theorem q8_no_comm_order3
    {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    (e : ↥Q ≃* QuaternionGroup 2) {u : X} (hu2 : u * u = 1)
    (hout : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹) {d : X} (hd3 : d ^ 3 = 1)
    (hdn : ∃ q ∈ Q, d * q * d⁻¹ ≠ q) : u * d ≠ d * u := by
  intro hcomm
  obtain ⟨q, hq, hqne⟩ := hdn
  have hd3' : d * d * d = 1 := by rw [← pow_three', hd3]
  refine q8aut_no_comm (uAut Q e u) (uAut Q e d) (uAut_fix Q e u hu2)
    (uAut_not_inner Q e u hout) ?_ ⟨e ⟨q, hq⟩, ?_⟩ ?_
  · intro y
    apply e.symm.injective
    apply Subtype.ext
    rw [uAut_apply, uAut_apply, uAut_apply]
    calc d * (d * (d * (e.symm y : X) * d⁻¹) * d⁻¹) * d⁻¹
        = (d * d * d) * (e.symm y : X) * (d * d * d)⁻¹ := by group
      _ = (e.symm y : X) := by rw [hd3']; simp
  · intro h
    have h1 := congrArg (fun z => ((e.symm z : ↥Q) : X)) h
    simp only [uAut_apply, MulEquiv.symm_apply_apply] at h1
    exact hqne h1
  · intro y
    apply e.symm.injective
    apply Subtype.ext
    rw [uAut_mul_apply, uAut_mul_apply, hcomm]

theorem q8_twisted_conj
    {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    (e : ↥Q ≃* QuaternionGroup 2) {u : X} (hu2 : u * u = 1)
    (hout : ¬ ∃ q ∈ Q, ∀ y ∈ Q, u * y * u⁻¹ = q * y * q⁻¹) :
    ∀ q ∈ Q, q * (u * q * u⁻¹) = 1 → ∃ d ∈ Q, q = d * (u * d * u⁻¹)⁻¹ := by
  intro q hq hqq
  have h1 : e ⟨q, hq⟩ * uAut Q e u (e ⟨q, hq⟩) = 1 := by
    apply e.symm.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, uAut_apply, MulEquiv.symm_apply_apply, map_one]
    exact hqq
  obtain ⟨d0, hd0⟩ := q8aut_twisted (uAut Q e u) (uAut_fix Q e u hu2) (uAut_not_inner Q e u hout)
    _ h1
  refine ⟨(e.symm d0 : X), (e.symm d0).2, ?_⟩
  have h2 := congrArg (fun z => ((e.symm z : ↥Q) : X)) hd0
  simp only [uAut_apply, map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h2
  exact h2

end CFSG.GH74.E2
