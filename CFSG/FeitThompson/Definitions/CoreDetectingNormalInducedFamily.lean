module

public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] [Fintype L] (K : Subgroup L)

noncomputable def indFamDetect (H : Subgroup K) : Set (L → ℂ) := indFam K (irrDetect ℂ H)

theorem indFamDetect_eq_indFam (H : Subgroup K) :
    indFamDetect K H = indFam K (irrDetect ℂ H) := (rfl)

theorem mem_indFamDetect {H : Subgroup K} {f : L → ℂ} :
    f ∈ indFamDetect K H ↔ ∃ θ ∈ irrDetect ℂ H, indClassFun K θ = f := by
  rw [indFamDetect_eq_indFam]; exact mem_indFam K

theorem mem_indFamDetect_iff_values {H : Subgroup K} {f : L → ℂ} :
    f ∈ indFamDetect K H ↔
      ∃ θ ∈ irrChar ℂ K, (∃ x ∈ H, θ x ≠ θ 1) ∧ indClassFun K θ = f := by
  simp only [mem_indFamDetect, mem_irrDetect_iff_values]
  tauto

theorem mem_indFamDetect_subgroupOf {H : Subgroup L} {f : L → ℂ} :
    f ∈ indFamDetect K (H.subgroupOf K) ↔
      ∃ θ ∈ irrChar ℂ K, (∃ x : K, (x : L) ∈ H ∧ θ x ≠ θ 1) ∧ indClassFun K θ = f := by
  simp only [mem_indFamDetect_iff_values, Subgroup.mem_subgroupOf]

theorem indClassFun_mem_indFamDetect {H : Subgroup K} {θ : K → ℂ} (hθ : θ ∈ irrDetect ℂ H) :
    indClassFun K θ ∈ indFamDetect K H :=
  (mem_indFamDetect K).2 ⟨θ, hθ, rfl⟩

theorem indFamDetect_subset_indFam_irrChar (H : Subgroup K) :
    indFamDetect K H ⊆ indFam K (irrChar ℂ K) := by
  rw [indFamDetect_eq_indFam]; exact indFam_mono K (irrDetect_subset_irrChar H)

theorem indFamDetect_mono {H H' : Subgroup K} (h : H ≤ H') :
    indFamDetect K H ⊆ indFamDetect K H' := by
  rw [indFamDetect_eq_indFam, indFamDetect_eq_indFam]
  exact indFam_mono K (irrDetect_mono h)

theorem indFam_irrKer_subset_indFamDetect (H M : Subgroup K) :
    indFam K (irrKer ℂ H M) ⊆ indFamDetect K H := by
  rw [indFamDetect_eq_indFam]; exact indFam_mono K (irrKer_subset_irrDetect H M)

@[simp] theorem indFamDetect_bot : indFamDetect K (⊥ : Subgroup K) = ∅ := by
  rw [indFamDetect_eq_indFam, irrDetect_bot, indFam_empty]

theorem conj_eq_of_mem_indFamDetect {H : Subgroup K} {f : L → ℂ} (hf : f ∈ indFamDetect K H)
    (x y : L) : f (x * y * x⁻¹) = f y :=
  conj_eq_of_mem_indFam K (indFamDetect_subset_indFam_irrChar K H hf) x y

theorem eq_zero_of_mem_indFamDetect_of_notMem [K.Normal] {H : Subgroup K} {f : L → ℂ}
    (hf : f ∈ indFamDetect K H) {y : L} (hy : y ∉ K) : f y = 0 :=
  eq_zero_of_mem_indFam_of_notMem K (indFamDetect_subset_indFam_irrChar K H hf) hy

end CFSG.FeitThompson
