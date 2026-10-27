module

public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

variable {L : Type*} [Group L] [Fintype L] (H : Subgroup L) [H.Normal]

theorem eq_zero_of_mem_span_indFam_of_notMem {X : Set (H → ℂ)} {S : Set (L → ℂ)}
    (hS : S ⊆ indFam H X) {f : L → ℂ} (hf : f ∈ Submodule.span ℤ S) {y : L} (hy : y ∉ H) :
    f y = 0 := by
  have h : Submodule.span ℤ S ≤ LinearMap.ker (LinearMap.proj y : (L → ℂ) →ₗ[ℤ] ℂ) := by
    rw [Submodule.span_le]
    intro g hg
    simpa using eq_zero_of_mem_indFam_of_notMem H (hS hg) hy
  simpa using h hf

theorem mem_intSpanZeroAtOne_iff_of_subset_indFam {X : Set (H → ℂ)} {S : Set (L → ℂ)}
    (hS : S ⊆ indFam H X) {f : L → ℂ} :
    f ∈ intSpanZeroAtOne S ↔
      f ∈ Submodule.span ℤ S ∧ ∀ y : L, y ∉ (H : Set L) \ {1} → f y = 0 := by
  rw [mem_intSpanZeroAtOne]
  refine and_congr_right fun hf => ⟨fun h1 y hy => ?_, fun h => h 1 (by simp)⟩
  by_cases hmem : y ∈ H
  · rw [show y = 1 by simpa [hmem] using hy, h1]
  · exact eq_zero_of_mem_span_indFam_of_notMem H hS hf hmem

theorem coe_intSpanZeroAtOne_eq_of_subset_indFam {X : Set (H → ℂ)} {S : Set (L → ℂ)}
    (hS : S ⊆ indFam H X) :
    (intSpanZeroAtOne S : Set (L → ℂ)) =
      {f | f ∈ Submodule.span ℤ S ∧ Function.support f ⊆ (H : Set L) \ {1}} := by
  ext f
  rw [SetLike.mem_coe, mem_intSpanZeroAtOne_iff_of_subset_indFam H hS]
  exact and_congr_right fun _ =>
    ⟨Function.support_subset_iff'.2, Function.support_subset_iff'.1⟩

omit [H.Normal] in
theorem sub_smul_apply_one_mem_intSpanZeroAtOne {S : Set (L → ℂ)} (hS : S ⊆ indFam H (Irr H))
    {φ ψ : L → ℂ} (hφ : φ ∈ S) (hψ : ψ ∈ S) :
    ψ 1 • φ - φ 1 • ψ ∈ intSpanZeroAtOne S := by
  obtain ⟨a, -, -, ha⟩ := exists_apply_one_eq_of_mem_indFam H (hS hφ)
  obtain ⟨b, -, -, hb⟩ := exists_apply_one_eq_of_mem_indFam H (hS hψ)
  refine mem_intSpanZeroAtOne.2 ⟨?_, ?_⟩
  · have key : ψ 1 • φ - φ 1 • ψ = (b : ℤ) • φ - (a : ℤ) • ψ := by
      rw [ha, hb, ← Int.cast_natCast (R := ℂ) b, ← Int.cast_natCast (R := ℂ) a,
        Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [key]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hφ))
      (Submodule.smul_mem _ _ (Submodule.subset_span hψ))
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem support_sub_smul_apply_one_subset {S : Set (L → ℂ)} (hS : S ⊆ indFam H (Irr H))
    {φ ψ : L → ℂ} (hφ : φ ∈ S) (hψ : ψ ∈ S) :
    Function.support (ψ 1 • φ - φ 1 • ψ) ⊆ (H : Set L) \ {1} := by
  have h := sub_smul_apply_one_mem_intSpanZeroAtOne H hS hφ hψ
  rw [← SetLike.mem_coe, coe_intSpanZeroAtOne_eq_of_subset_indFam H hS] at h
  exact h.2

end NormalInducedFamily

end CFSG.FeitThompson
