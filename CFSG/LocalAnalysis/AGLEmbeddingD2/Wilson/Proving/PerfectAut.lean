module

public import Mathlib.GroupTheory.IsPerfect

public section

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem eq_one_of_isPerfect_of_mul_inv_mem_center {K : Type*} [Group K] (hK : Group.IsPerfect K)
    (α : MulAut K) (h : ∀ k : K, α k * k⁻¹ ∈ Subgroup.center K) : α = 1 := by
  let ζ : K →* Subgroup.center K :=
    { toFun := fun k => ⟨α k * k⁻¹, h k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro k l
        apply Subtype.ext
        have hz : ∀ g : K, g * (α l * l⁻¹) = (α l * l⁻¹) * g :=
          fun g => Subgroup.mem_center_iff.mp (h l) g
        show α (k * l) * (k * l)⁻¹ = (α k * k⁻¹) * (α l * l⁻¹)
        calc α (k * l) * (k * l)⁻¹ = α k * ((α l * l⁻¹) * k⁻¹) := by
              rw [map_mul]; group
          _ = α k * (k⁻¹ * (α l * l⁻¹)) := by rw [hz k⁻¹]
          _ = (α k * k⁻¹) * (α l * l⁻¹) := by group }
  have hcomm : ∀ x y : K, ζ ⁅x, y⁆ = 1 := by
    intro x y
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (ζ y).2 (ζ x).1
  have htop : (⊤ : Subgroup K) ≤ ζ.ker := by
    have hc : ⁅(⊤ : Subgroup K), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← hc]
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    exact MonoidHom.mem_ker.mpr (hcomm x y)
  ext k
  have hk : ζ k = 1 := MonoidHom.mem_ker.mp (htop (Subgroup.mem_top k))
  have h1 : α k * k⁻¹ = 1 := congrArg Subtype.val hk
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
