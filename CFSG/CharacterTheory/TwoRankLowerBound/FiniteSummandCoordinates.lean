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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def supportedCoordinateSubmodule {ring index : Type*} [Ring ring]
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)] [∀ label, Module ring (vector label)]
    (support : Set index) : Submodule ring (∀ label, vector label) where
  carrier := {value | ∀ label, label ∉ support → value label = 0}
  zero_mem' := by simp
  add_mem' := by
    intro left right hleft hright label hnot
    simp only [Pi.add_apply, hleft label hnot, hright label hnot, add_zero]
  smul_mem' := by
    intro scalar value hvalue label hnot
    simp only [Pi.smul_apply, hvalue label hnot, smul_zero]

noncomputable def finiteProductConsEquiv {ring : Type*} [Ring ring] {size : ℕ}
    (vector : Fin (size + 1) → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ring (vector label)] :
    (∀ label, vector label) ≃ₗ[ring] (vector 0 × (∀ label : Fin size, vector label.succ)) where
  toFun := fun value => (value 0, fun label => value label.succ)
  invFun := fun value => Fin.cons value.1 value.2
  left_inv := by
    intro value
    funext label
    refine Fin.cases ?_ (fun label => ?_) label <;> simp
  right_inv := by
    intro value
    exact Prod.ext (by simp) (by funext label; simp)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def supportedCoordinatesConsEquiv {ring : Type*} [Ring ring] {size : ℕ}
    (vector : Fin (size + 1) → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ring (vector label)] (support : Set (Fin size)) :
    supportedCoordinateSubmodule (ring := ring) vector
      {label | label = 0 ∨ ∃ member ∈ support, member.succ = label}
      ≃ₗ[ring] (vector 0 × supportedCoordinateSubmodule (ring := ring)
        (fun label : Fin size => vector label.succ) support) := by
  let sourceSupport : Set (Fin (size + 1)) :=
    {label | label = 0 ∨ ∃ member ∈ support, member.succ = label}
  let forward : supportedCoordinateSubmodule (ring := ring) vector sourceSupport →ₗ[ring]
      (vector 0 × supportedCoordinateSubmodule (ring := ring)
        (fun label : Fin size => vector label.succ) support) :=
    { toFun := fun value => (value.val 0, ⟨fun label => value.val label.succ, by
        intro label hnot
        apply value.property
        simpa [sourceSupport] using hnot⟩)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let backward : (vector 0 × supportedCoordinateSubmodule (ring := ring)
      (fun label : Fin size => vector label.succ) support)
      →ₗ[ring] supportedCoordinateSubmodule (ring := ring) vector sourceSupport :=
    { toFun := fun value => ⟨Fin.cons value.1 value.2.val, by
        intro label
        refine Fin.cases ?_ (fun member => ?_) label
        · intro hnot
          exact False.elim (hnot (Or.inl rfl))
        · intro hnot
          simp only [Fin.cons_succ]
          apply value.2.property
          intro hmember
          exact hnot (Or.inr ⟨member, hmember, rfl⟩)⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        funext label
        refine Fin.cases ?_ (fun member => ?_) label <;> simp
      map_smul' := by
        intro scalar value
        apply Subtype.ext
        funext label
        refine Fin.cases ?_ (fun member => ?_) label <;> simp }
  refine LinearEquiv.ofLinearMap forward backward ?_ ?_
  · apply LinearMap.ext
    intro value
    exact Prod.ext (by simp [forward, backward]) (by apply Subtype.ext; funext label; simp [forward, backward])
  · apply LinearMap.ext
    intro value
    apply Subtype.ext
    funext label
    refine Fin.cases ?_ (fun member => ?_) label <;> simp [forward, backward]

noncomputable def supportedCoordinatesTailEquiv {ring : Type*} [Ring ring] {size : ℕ}
    (vector : Fin (size + 1) → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ring (vector label)] (support : Set (Fin size)) :
    supportedCoordinateSubmodule (ring := ring) vector {label | ∃ member ∈ support, member.succ = label}
      ≃ₗ[ring] supportedCoordinateSubmodule (ring := ring)
        (fun label : Fin size => vector label.succ) support := by
  let sourceSupport : Set (Fin (size + 1)) := {label | ∃ member ∈ support, member.succ = label}
  let forward : supportedCoordinateSubmodule (ring := ring) vector sourceSupport →ₗ[ring]
      supportedCoordinateSubmodule (ring := ring) (fun label : Fin size => vector label.succ) support :=
    { toFun := fun value => ⟨fun label => value.val label.succ, by
        intro label hnot
        apply value.property
        simpa [sourceSupport] using hnot⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let backward : supportedCoordinateSubmodule (ring := ring)
      (fun label : Fin size => vector label.succ) support →ₗ[ring]
      supportedCoordinateSubmodule (ring := ring) vector sourceSupport :=
    { toFun := fun value => ⟨Fin.cons 0 value.val, by
        intro label
        refine Fin.cases ?_ (fun member => ?_) label
        · intro _
          simp
        · intro hnot
          simp only [Fin.cons_succ]
          apply value.property
          intro hmember
          exact hnot ⟨member, hmember, rfl⟩⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        funext label
        refine Fin.cases ?_ (fun member => ?_) label <;> simp
      map_smul' := by
        intro scalar value
        apply Subtype.ext
        funext label
        refine Fin.cases ?_ (fun member => ?_) label <;> simp }
  refine LinearEquiv.ofLinearMap forward backward ?_ ?_
  · apply LinearMap.ext
    intro value
    apply Subtype.ext
    funext label
    simp [forward, backward]
  · apply LinearMap.ext
    intro value
    apply Subtype.ext
    funext label
    refine Fin.cases ?_ (fun member => ?_) label
    · have hzero := value.property 0 (by simp)
      simpa [forward, backward] using hzero.symm
    · simp [forward, backward]

noncomputable def transportedProjection {ring source target : Type*} [Ring ring]
    [AddCommGroup source] [AddCommGroup target] [Module ring source] [Module ring target]
    (equivalence : source ≃ₗ[ring] target) (projection : Module.End ring source) : Module.End ring target :=
  equivalence.toLinearMap.comp (projection.comp equivalence.symm.toLinearMap)

theorem transportedProjection_isIdempotent {ring source target : Type*} [Ring ring]
    [AddCommGroup source] [AddCommGroup target] [Module ring source] [Module ring target]
    (equivalence : source ≃ₗ[ring] target) (projection : Module.End ring source)
    (hidempotent : IsIdempotentElem projection) :
    IsIdempotentElem (transportedProjection equivalence projection) := by
  apply isIdempotentElem_iff.mpr
  apply LinearMap.ext
  intro value
  have hvalue := congrArg (fun operator : Module.End ring source => operator (equivalence.symm value))
    hidempotent.eq
  simpa only [transportedProjection, Module.End.mul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using congrArg equivalence hvalue

theorem transportedProjection_range_equiv {ring source target : Type*} [Ring ring]
    [AddCommGroup source] [AddCommGroup target] [Module ring source] [Module ring target]
    (equivalence : source ≃ₗ[ring] target) (projection : Module.End ring source) :
    Nonempty (projection.range ≃ₗ[ring] (transportedProjection equivalence projection).range) := by
  have hrange : Submodule.map equivalence.toLinearMap projection.range =
      (transportedProjection equivalence projection).range := by
    rw [transportedProjection, LinearMap.range_comp, LinearEquiv.range_comp]
  exact ⟨equivalence.ofSubmodules _ _ hrange⟩

end CFSG.TwoRankLowerBound.Helpers
