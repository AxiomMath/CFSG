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

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev PieceQ (F F' : Submodule K V) : Type _ := ↥F' ⧸ F.comap F'.subtype

@[expose] def stabPair (F F' : Submodule K V) : Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | (∀ v ∈ F, (g : Module.End K V) v ∈ F) ∧ (∀ v ∈ F', (g : Module.End K V) v ∈ F') ∧
    (∀ v ∈ F, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ F) ∧
    (∀ v ∈ F', ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ F')}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [Units.val_mul, Module.End.mul_apply]; exact ha1 _ (hb1 v hv)
    · rw [Units.val_mul, Module.End.mul_apply]; exact ha2 _ (hb2 v hv)
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]; exact hb3 _ (ha3 v hv)
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]; exact hb4 _ (ha4 v hv)
  one_mem' := ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv,
    fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4⟩
    exact ⟨fun v hv => ha3 v hv, fun v hv => ha4 v hv, fun v hv => by simpa using ha1 v hv,
      fun v hv => by simpa using ha2 v hv⟩

theorem mem_stabPair {F F' : Submodule K V} {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ stabPair F F' ↔ (∀ v ∈ F, (g : Module.End K V) v ∈ F) ∧
      (∀ v ∈ F', (g : Module.End K V) v ∈ F') ∧
      (∀ v ∈ F, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ F) ∧
      (∀ v ∈ F', ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ F') :=
  Iff.rfl

@[expose] noncomputable def quotAct {F F' : Submodule K V} (g : Module.End K V)
    (hF : ∀ v ∈ F, g v ∈ F) (hF' : ∀ v ∈ F', g v ∈ F') : PieceQ F F' →ₗ[K] PieceQ F F' :=
  Submodule.mapQ (F.comap F'.subtype) (F.comap F'.subtype) (g.restrict hF') (by
    intro v hv
    simpa [Submodule.mem_comap] using hF _ hv)

theorem quotAct_mk {F F' : Submodule K V} (g : Module.End K V) (hF : ∀ v ∈ F, g v ∈ F)
    (hF' : ∀ v ∈ F', g v ∈ F') (v : ↥F') :
    quotAct g hF hF' (Submodule.Quotient.mk v) = Submodule.Quotient.mk ⟨g v, hF' v v.2⟩ := rfl

@[expose] noncomputable def quotEnd (F F' : Submodule K V) :
    stabPair F F' →* Module.End K (PieceQ F F') where
  toFun g := quotAct ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) g.2.1 g.2.2.1
  map_one' := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H v => rfl
  map_mul' g h := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H v => rfl

theorem quotEnd_mk {F F' : Submodule K V} (g : stabPair F F') (v : ↥F') :
    quotEnd F F' g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v,
        g.2.2.1 v v.2⟩ := rfl

@[expose] noncomputable def quotGL (F F' : Submodule K V) :
    stabPair F F' →* LinearMap.GeneralLinearGroup K (PieceQ F F') :=
  (quotEnd F F').toHomUnits

theorem coe_quotGL {F F' : Submodule K V} (g : stabPair F F') :
    ((quotGL F F' g : LinearMap.GeneralLinearGroup K (PieceQ F F')) : Module.End K (PieceQ F F')) =
      quotEnd F F' g := rfl

end CFSG.HardMathSupport.Curtis.UnitaryLevi
