module

public import CFSG.HardMathSupport.RichardWeiss.Proving.AltFiveGeneration

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
theorem altFive_conj_pair : ∀ σ τ : Perm (Fin 5), σ.support.card = 3 → τ.support.card = 3 →
    (σ.support ∩ τ.support).card = 1 →
    ∃ π : Perm (Fin 5), π * σ * π⁻¹ = altFiveUPerm ∧ π * τ * π⁻¹ = altFiveVPerm := by
  decide +kernel

theorem altFive_perm_le_closure :
    alternatingGroup (Fin 5) ≤
      Subgroup.closure ({altFiveUPerm, altFiveVPerm} : Set (Perm (Fin 5))) := by
  have key : ∀ x ∈ Subgroup.closure ({altFiveU, altFiveV} : Set (alternatingGroup (Fin 5))),
      (x : Perm (Fin 5)) ∈ Subgroup.closure ({altFiveUPerm, altFiveVPerm} : Set (Perm (Fin 5))) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [altFiveU_val]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [altFiveV_val]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    | one => simp
    | mul a b _ _ iha ihb => rw [Subgroup.coe_mul]; exact mul_mem iha ihb
    | inv a _ iha => rw [Subgroup.coe_inv]; exact inv_mem iha
  intro g hg
  exact key ⟨g, hg⟩ (by rw [altFive_closure_pair_eq_top]; exact Subgroup.mem_top _)

theorem closure_pair_threeCycles_eq_alt5 (σ τ : Perm (Fin 5)) (hσ : σ.support.card = 3)
    (hτ : τ.support.card = 3) (hst : (σ.support ∩ τ.support).card = 1) :
    Subgroup.closure ({σ, τ} : Set (Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  obtain ⟨π, hπσ, hπτ⟩ := altFive_conj_pair σ τ hσ hτ hst
  have hσA : σ ∈ alternatingGroup (Fin 5) :=
    IsThreeCycle.mem_alternatingGroup (card_support_eq_three_iff.mp hσ)
  have hτA : τ ∈ alternatingGroup (Fin 5) :=
    IsThreeCycle.mem_alternatingGroup (card_support_eq_three_iff.mp hτ)
  have hφ : ∀ y ∈ Subgroup.closure ({altFiveUPerm, altFiveVPerm} : Set (Perm (Fin 5))),
      π⁻¹ * y * π ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 5))) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have h : π⁻¹ * altFiveUPerm * π = σ := by rw [← hπσ]; simp [mul_assoc]
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · have h : π⁻¹ * altFiveVPerm * π = τ := by rw [← hπτ]; simp [mul_assoc]
        rw [h]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    | one => simp
    | mul a b _ _ iha ihb =>
      have h : π⁻¹ * (a * b) * π = (π⁻¹ * a * π) * (π⁻¹ * b * π) := by simp [mul_assoc]
      rw [h]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have h : π⁻¹ * a⁻¹ * π = (π⁻¹ * a * π)⁻¹ := by simp [mul_assoc]
      rw [h]
      exact inv_mem iha
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hσA
    · exact hτA
  · intro g hg
    have hpi : π * g * π⁻¹ ∈ alternatingGroup (Fin 5) :=
      (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem g hg π
    have hmem := hφ (π * g * π⁻¹) (altFive_perm_le_closure hpi)
    have h : π⁻¹ * (π * g * π⁻¹) * π = g := by simp [mul_assoc]
    rwa [h] at hmem

end CFSG.HardMathSupport.RichardWeiss.Proving

end
