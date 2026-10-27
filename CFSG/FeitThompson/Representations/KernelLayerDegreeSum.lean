module

public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {K : Type*} [Group K]

theorem irrKer_eq_diff (H M : Subgroup K) :
    irrKer ℂ H M = irrTrivialOn M \ irrTrivialOn H := by
  ext χ
  simp only [mem_irrKer_iff_values, Set.mem_sdiff, mem_irrTrivialOn, ← Irr_eq_irrChar, not_and]
  constructor
  · rintro ⟨h1, h2, x, hx, hne⟩
    exact ⟨⟨h1, h2⟩, fun _ h => hne (h x hx)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hc
    push Not at hc
    exact h3 h1 hc

theorem finite_irrKer [Finite K] (H M : Subgroup K) : (irrKer ℂ H M).Finite := by
  rw [irrKer_eq_diff]
  exact (finite_irrTrivialOn (N := M)).subset Set.sdiff_subset

noncomputable def irrKerFinset [Finite K] (H M : Subgroup K) : Finset (K → ℂ) :=
  (finite_irrKer H M).toFinset

@[simp]
theorem mem_irrKerFinset [Finite K] {H M : Subgroup K} {χ : K → ℂ} :
    χ ∈ irrKerFinset H M ↔ χ ∈ irrKer ℂ H M :=
  Set.Finite.mem_toFinset _

theorem irrKerFinset_eq_sdiff [Finite K] [DecidableEq (K → ℂ)] (H M : Subgroup K) :
    irrKerFinset H M = irrTrivialOnFinset M \ irrTrivialOnFinset H := by
  ext χ
  simp [irrKer_eq_diff]

theorem irrTrivialOnFinset_subset_of_le [Finite K] {H M : Subgroup K} (hMH : M ≤ H) :
    irrTrivialOnFinset H ⊆ irrTrivialOnFinset (G := K) M := by
  intro χ hχ
  rw [mem_irrTrivialOnFinset, mem_irrTrivialOn] at hχ ⊢
  exact ⟨hχ.1, fun n hn => hχ.2 n (hMH hn)⟩

theorem sum_sq_degree_irrKer_eq_sub [Finite K] {H M : Subgroup K} [M.Normal] [H.Normal]
    (hMH : M ≤ H) :
    ∑ χ ∈ irrKerFinset H M, χ 1 ^ 2 = (M.index : ℂ) - (H.index : ℂ) := by
  classical
  rw [irrKerFinset_eq_sdiff, Finset.sum_sdiff_eq_sub (irrTrivialOnFinset_subset_of_le hMH),
    sum_sq_degree_irrTrivialOn_eq_index, sum_sq_degree_irrTrivialOn_eq_index]

theorem sum_sq_degree_irrKer [Finite K] {H M : Subgroup K} [M.Normal] [H.Normal] (hMH : M ≤ H) :
    ∑ χ ∈ irrKerFinset H M, χ 1 ^ 2 = (H.index : ℂ) * ((M.relIndex H : ℂ) - 1) := by
  rw [sum_sq_degree_irrKer_eq_sub hMH, ← Subgroup.relIndex_mul_index hMH]
  push_cast
  ring

theorem irrKerFinset_self [Finite K] (H : Subgroup K) : irrKerFinset H H = ∅ := by
  ext χ
  simp [irrKer_eq_empty_of_le (le_refl H)]

end CFSG.FeitThompson
