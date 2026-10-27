module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

private def alt5Alpha : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def alt5Xi : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private lemma alt5_witness :
    ∃ α ξ : alternatingGroup (Fin 5), α * α = 1 ∧ α ≠ 1 ∧ ξ ^ 3 = 1 ∧ ξ ≠ 1 ∧
      (ξ * α * ξ⁻¹) * α = α * (ξ * α * ξ⁻¹) :=
  ⟨alt5Alpha, alt5Xi, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

private lemma exists_map_of_exists {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f)
    (h : ∃ a x : M, a * a = 1 ∧ a ≠ 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧
      (x * a * x⁻¹) * a = a * (x * a * x⁻¹)) :
    ∃ a x : N, a * a = 1 ∧ a ≠ 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧
      (x * a * x⁻¹) * a = a * (x * a * x⁻¹) := by
  obtain ⟨a, x, haa, ha1, hx3, hx1, hcomm⟩ := h
  refine ⟨f a, f x, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_one] using congrArg f haa
  · intro hcon
    exact ha1 (hf (by simpa only [map_one] using hcon))
  · simpa only [map_pow, map_one] using congrArg f hx3
  · intro hcon
    exact hx1 (hf (by simpa only [map_one] using hcon))
  · simpa only [map_mul, map_inv] using congrArg f hcomm

theorem exists_involution_order_three_commute {E : Type*} [Group E] (A : Subgroup E)
    (hA : Nonempty (A ≃* alternatingGroup (Fin 5))) :
    ∃ a x : E, a * a = 1 ∧ a ≠ 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧
      (x * a * x⁻¹) * a = a * (x * a * x⁻¹) := by
  obtain ⟨φ⟩ := hA
  obtain ⟨a, x, haa, ha1, hx3, hx1, hcomm⟩ :=
    exists_map_of_exists φ.symm.toMonoidHom φ.symm.injective alt5_witness
  exact exists_map_of_exists (Subgroup.subtype A) Subtype.coe_injective
    ⟨a, x, haa, ha1, hx3, hx1, hcomm⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
