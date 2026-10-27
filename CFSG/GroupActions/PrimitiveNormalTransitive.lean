module

public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG.GroupActions

theorem isPretransitive_of_normal_ne_bot
    {G Ω : Type*} [Group G] [MulAction G Ω] [Nonempty Ω]
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    MulAction.IsPretransitive N Ω := by
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  have hnotfixed : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
    intro x
    have hx : x ∈ MulAction.fixedPoints N Ω := hfixed.symm ▸ Set.mem_univ x
    exact (hx a).trans (hx b).symm
  exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hnotfixed

end CFSG.GroupActions
