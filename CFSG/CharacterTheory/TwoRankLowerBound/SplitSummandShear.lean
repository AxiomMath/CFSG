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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def endomorphismUnitLinearEquiv {ring vector : Type*} [Ring ring]
    [AddCommGroup vector] [Module ring vector] (unit : (Module.End ring vector)ˣ) :
    vector ≃ₗ[ring] vector :=
  LinearEquiv.ofLinearMap (unit : Module.End ring vector) (unit⁻¹ : (Module.End ring vector)ˣ)
    unit.val_inv unit.inv_val

@[expose] noncomputable def splitCoordinateShear {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (sectionMap : left →ₗ[ring] left × right)
    (hfirst : ∀ element, (sectionMap element).1 = element) :
    (left × right) ≃ₗ[ring] (left × right) where
  toFun := fun element => sectionMap element.1 + (0, element.2)
  invFun := fun element => (element.1, element.2 - (sectionMap element.1).2)
  left_inv := by
    intro element
    ext <;> simp [hfirst]
  right_inv := by
    intro element
    ext <;> simp [hfirst]
  map_add' := by
    intro first second
    ext <;> simp [hfirst]
    abel
  map_smul' := by
    intro scalar element
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, Prod.smul_mk, smul_zero,
      RingHom.id_apply]

theorem idempotent_coordinate_section {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (hidempotent : IsIdempotentElem projection)
    (hinvertible : IsUnit ((LinearMap.fst ring left right).comp
      (projection.comp (LinearMap.inl ring left right)))) :
    ∃ sectionMap : left →ₗ[ring] left × right,
      (∀ element, (sectionMap element).1 = element) ∧
      ∀ element, projection (sectionMap element) = sectionMap element := by
  obtain ⟨unit, hunit⟩ := hinvertible
  let sectionMap := projection.comp ((LinearMap.inl ring left right).comp
    (endomorphismUnitLinearEquiv unit).symm.toLinearMap)
  refine ⟨sectionMap, ?_, ?_⟩
  · intro element
    have hvalue := congrArg (fun operator : Module.End ring left =>
      operator ((endomorphismUnitLinearEquiv unit).symm element)) hunit
    change (unit : Module.End ring left) ((endomorphismUnitLinearEquiv unit).symm element) =
      (sectionMap element).1 at hvalue
    exact hvalue.symm.trans ((endomorphismUnitLinearEquiv unit).apply_symm_apply element)
  · intro element
    exact congrArg (fun operator : Module.End ring (left × right) =>
      operator ((LinearMap.inl ring left right)
        ((endomorphismUnitLinearEquiv unit).symm element))) hidempotent.eq

@[expose] noncomputable def conjugateProjection {ring vector : Type*} [Ring ring]
    [AddCommGroup vector] [Module ring vector] (equivalence : vector ≃ₗ[ring] vector)
    (projection : Module.End ring vector) : Module.End ring vector :=
  equivalence.symm.toLinearMap.comp (projection.comp equivalence.toLinearMap)

theorem conjugateProjection_isIdempotent {ring vector : Type*} [Ring ring]
    [AddCommGroup vector] [Module ring vector] (equivalence : vector ≃ₗ[ring] vector)
    (projection : Module.End ring vector) (hidempotent : IsIdempotentElem projection) :
    IsIdempotentElem (conjugateProjection equivalence projection) := by
  apply isIdempotentElem_iff.mpr
  ext element
  have hvalue := congrArg (fun operator : Module.End ring vector => operator (equivalence element))
    hidempotent.eq
  simpa only [conjugateProjection, Module.End.mul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using congrArg equivalence.symm hvalue

theorem shear_conjugateProjection_fixes_left {ring left right : Type*} [Ring ring]
    [AddCommGroup left] [AddCommGroup right] [Module ring left] [Module ring right]
    (projection : Module.End ring (left × right)) (sectionMap : left →ₗ[ring] left × right)
    (hfirst : ∀ element, (sectionMap element).1 = element)
    (hfixed : ∀ element, projection (sectionMap element) = sectionMap element) (element : left) :
    conjugateProjection (splitCoordinateShear sectionMap hfirst) projection (element, 0) =
      (element, 0) := by
  change (splitCoordinateShear sectionMap hfirst).symm
    (projection (sectionMap element + (0, 0))) = _
  simp only [Prod.mk_zero_zero, add_zero, hfixed]
  change ((sectionMap element).1,
    (sectionMap element).2 - (sectionMap (sectionMap element).1).2) = _
  rw [hfirst, sub_self]

end CFSG.TwoRankLowerBound.Helpers
