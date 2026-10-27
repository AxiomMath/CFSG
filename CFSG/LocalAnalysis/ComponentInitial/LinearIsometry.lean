module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.LocalAnalysis.ComponentInitial

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

@[expose] def bilinIsometryGroup (B : LinearMap.BilinForm R M) :
    Subgroup (LinearMap.GeneralLinearGroup R M) where
  carrier := {g | ∀ x y, B ((g : M →ₗ[R] M) x) ((g : M →ₗ[R] M) y) = B x y}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h := hg (((g⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) x)
      (((g⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) y)
    simp only [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h
    exact h.symm

theorem mem_bilinIsometryGroup {B : LinearMap.BilinForm R M}
    {g : LinearMap.GeneralLinearGroup R M} :
    g ∈ bilinIsometryGroup B ↔ ∀ x y, B ((g : M →ₗ[R] M) x) ((g : M →ₗ[R] M) y) = B x y :=
  Iff.rfl

end CFSG.LocalAnalysis.ComponentInitial
