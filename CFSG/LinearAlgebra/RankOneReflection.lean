module

public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public noncomputable section

namespace CFSG.LinearAlgebra

theorem exists_reflection_of_finrank_range_one_sub_eq_one {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] {f : Module.End K V}
    (hf : f ^ 2 = 1) (hr : Module.finrank K (LinearMap.range (1 - f)) = 1) :
    ∃ (x : V) (φ : Module.Dual K V) (hφ : φ x = 2),
      x ≠ 0 ∧ f = (Module.reflection hφ).toLinearMap := by
  obtain ⟨x, hx0⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp (hr ▸ Nat.zero_lt_one)
  have hx : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hspan : LinearMap.range (1 - f) = Submodule.span K {(x : V)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hr x.2 hx
  have hmem (v : V) : (1 - f) v ∈ Submodule.span K {(x : V)} := by
    rw [← hspan]
    exact LinearMap.mem_range_self _ v
  let φ : Module.Dual K V := (LinearEquiv.coord K V (x : V) hx).toLinearMap ∘ₗ
    (1 - f).codRestrict (Submodule.span K {(x : V)}) hmem
  have hφ (v : V) : φ v • (x : V) = v - f v := by
    exact LinearEquiv.coord_apply_smul K V (x : V) hx ⟨(1 - f) v, hmem v⟩
  have hff (v : V) : f (f v) = v := by
    have h := congrArg (fun g : Module.End K V => g v) hf
    simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using h
  have hxneg : f (x : V) = -(x : V) := by
    obtain ⟨v, hv⟩ := x.2
    rw [← hv, LinearMap.sub_apply, Module.End.one_apply, map_sub, hff]
    module
  have hpair : φ (x : V) = 2 := by
    have h : (φ (x : V) - 2) • (x : V) = 0 := by
      rw [sub_smul, hφ, hxneg]
      module
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hx)
  refine ⟨x, φ, hpair, hx, ?_⟩
  ext v
  change f v = Module.reflection hpair v
  rw [Module.reflection_apply, hφ]
  module

end CFSG.LinearAlgebra
