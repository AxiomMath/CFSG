module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

@[expose] def Real3 (X : Type*) [Group X] : Prop :=
  ∀ x : X, x ^ 3 = 1 → ∃ t : X, t * x * t⁻¹ = x⁻¹

theorem Real3.of_mulEquiv {X M : Type*} [Group X] [Group M] (e : X ≃* M) (h : Real3 M) :
    Real3 X := by
  intro x hx
  obtain ⟨s, hs⟩ := h (e x) (by rw [← map_pow, hx, map_one])
  refine ⟨e.symm s, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hs, map_inv]

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
