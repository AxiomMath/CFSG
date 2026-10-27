module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

@[expose] def chainStab (Q : Type*) [Group Q] : Subgroup (MulAut Q) where
  carrier := {α | (∀ x : Q, x⁻¹ * α x ∈ center Q) ∧ ∀ z ∈ center Q, α z = z}
  mul_mem' := by
    intro α β hα hβ
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · have h : x⁻¹ * (α * β) x = (x⁻¹ * β x) * ((β x)⁻¹ * α (β x)) := by
        simp [MulAut.mul_apply]
      rw [h]
      exact mul_mem (hβ.1 x) (hα.1 (β x))
    · rw [MulAut.mul_apply, hβ.2 z hz, hα.2 z hz]
  one_mem' := by
    refine ⟨fun x => ?_, fun z _ => rfl⟩
    simp
  inv_mem' := by
    intro α hα
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · have h := hα.1 (α⁻¹ x)
      have e : x⁻¹ * α⁻¹ x = ((α⁻¹ x)⁻¹ * α (α⁻¹ x))⁻¹ := by
        simp
      rw [e]
      exact inv_mem h
    · have h := hα.2 z hz
      change α.symm z = z
      conv_lhs => rw [← h]
      exact α.symm_apply_apply z

variable {Q : Type*} [Group Q]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
