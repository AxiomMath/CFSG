module

public import CFSG.GH74.KGroups.L33
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsDefs

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier

theorem model_relations :
    modelX ^ 8 = 1 ∧ modelX ^ 4 ≠ 1 ∧ modelY ^ 2 = 1 ∧ modelK ^ 2 = 1 ∧
      modelY * modelX * modelY⁻¹ = modelX ^ 3 ∧ modelK * modelX * modelK⁻¹ = modelX * modelX ^ 4 ∧
      modelY * modelK = modelK * modelY ∧ (modelX * modelY * modelK) ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem model_normalForm_injective :
    Function.Injective fun a : Fin 8 × Fin 2 × Fin 2 =>
      modelX ^ (a.1 : ℕ) * modelY ^ (a.2.1 : ℕ) * modelK ^ (a.2.2 : ℕ) := by
  decide +kernel

theorem model_P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  have hA : QA.originalSubgroup = Subgroup.closure {g | g ∈ [PA, PB, sg0]} := by
    rw [QA, certificate_originalSubgroup]
  rw [QP_closure, Subgroup.closure_le, hA]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp

theorem model_inner_mem :
    modelX ∈ QP.originalSubgroup ∧ modelY ∈ QP.originalSubgroup ∧
      modelG1 ∈ QP.originalSubgroup ∧ modelG2 ∈ QP.originalSubgroup ∧
      modelX ∈ QA.originalSubgroup ∧ modelY ∈ QA.originalSubgroup ∧
      modelG1 ∈ QA.originalSubgroup ∧ modelG2 ∈ QA.originalSubgroup := by
  have hX : modelX ∈ QP.originalSubgroup :=
    (mem_iff_sift QP QP_ok modelX).2 (by decide +kernel)
  have hY : modelY ∈ QP.originalSubgroup :=
    (mem_iff_sift QP QP_ok modelY).2 (by decide +kernel)
  have hG1 : modelG1 ∈ QP.originalSubgroup :=
    (mem_iff_sift QP QP_ok modelG1).2 (by decide +kernel)
  have hG2 : modelG2 ∈ QP.originalSubgroup :=
    (mem_iff_sift QP QP_ok modelG2).2 (by decide +kernel)
  exact ⟨hX, hY, hG1, hG2, model_P_le_A hX, model_P_le_A hY, model_P_le_A hG1,
    model_P_le_A hG2⟩

theorem model_outer_mem :
    modelK ∈ QA.originalSubgroup ∧ modelK ∉ QP.originalSubgroup := by
  refine ⟨?_, ?_⟩
  · exact (mem_iff_sift QA QA_ok modelK).2 (by decide +kernel)
  · rw [mem_iff_sift QP QP_ok modelK]
    decide +kernel

theorem model_three_one :
    modelG1 ^ 3 = 1 ∧ modelG1 * modelZ * modelG1⁻¹ = modelY ∧
      modelG1 * modelY * modelG1⁻¹ = modelZ * modelY ∧ modelG1 * modelK * modelG1⁻¹ = modelK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem model_three_two :
    modelG2 ^ 3 = 1 ∧ modelG2 * modelZ * modelG2⁻¹ = modelX ^ 2 * modelY ∧
      modelG2 * (modelX ^ 2 * modelY) * modelG2⁻¹ = modelZ * (modelX ^ 2 * modelY) ∧
      modelG2 * (modelZ * modelK) * modelG2⁻¹ = modelZ * modelK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.OddStandard.SmallF3.L33
