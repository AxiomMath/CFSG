module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.QuasithinUnique.A5

variable {G : Type*} [Group G]

structure IsTwoThree (Y : Subgroup G) (c : G) : Prop where
  isPGroup : IsPGroup 2 Y
  order_three : orderOf c = 3
  normalizes : c ∈ Subgroup.normalizer (Y : Set G)
  generated : ⁅Y, Subgroup.zpowers c⁆ = Y

theorem mem_map_conj_iff (Y : Subgroup G) (g x : G) :
    x ∈ Y.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Y := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem IsTwoThree.map_conj {Y : Subgroup G} {c : G} (h : IsTwoThree Y c) (g : G) :
    IsTwoThree (Y.map (MulAut.conj g).toMonoidHom) (g * c * g⁻¹) := by
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.isPGroup.of_equiv (Subgroup.equivMapOfInjective Y _ hf)
  · have := orderOf_injective (MulAut.conj g).toMonoidHom hf c
    simpa [MulAut.conj_apply, h.order_three] using this
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have hc := (Subgroup.mem_normalizer_iff.mp h.normalizes) (g⁻¹ * x * g)
    have e : g⁻¹ * (g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹) * g = c * (g⁻¹ * x * g) * c⁻¹ := by
      group
    rw [e]
    exact hc
  · have h1 : Subgroup.zpowers (g * c * g⁻¹) =
        (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]
    rw [h1, ← Subgroup.map_commutator, h.generated]

end CFSG.QuasithinUnique.A5
