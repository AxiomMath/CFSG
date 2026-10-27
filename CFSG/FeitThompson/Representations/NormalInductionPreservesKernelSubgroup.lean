module

public import CFSG.FeitThompson.Representations.NormalSubgroupInduction
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import Mathlib.Analysis.Complex.Norm
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
import Mathlib.Analysis.Complex.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInduction

open Module

theorem exists_degree_of_mem_irrChars {K : Type*} [Group K] [Finite K] {θ : K → ℂ}
    (hθ : θ ∈ irrChars K) : ∃ n : ℕ, θ 1 = (n : ℂ) ∧ ∀ k, ‖θ k‖ ≤ (n : ℝ) := by
  obtain ⟨V, _, _, ρ, _, _, rfl⟩ := mem_irrChars_iff.1 hθ
  exact ⟨finrank ℂ V, Representation.char_one ρ, fun k =>
    Representation.norm_character_le_finrank ρ (isOfFinOrder_of_finite k)⟩

theorem eq_of_norm_le_of_sum_eq {ι : Type*} [Fintype ι] {a : ι → ℂ} {r : ℝ}
    (hle : ∀ i, ‖a i‖ ≤ r) (hsum : ∑ i, a i = ∑ _i : ι, (r : ℂ)) (i : ι) :
    a i = (r : ℂ) := by
  have hre : ∀ j ∈ Finset.univ, (a j).re ≤ r := fun j _ =>
    le_trans (Complex.re_le_norm (a j)) (hle j)
  have hsumre : ∑ j, (a j).re = ∑ _j : ι, r := by
    have h := congrArg Complex.re hsum
    simpa [Complex.re_sum] using h
  have h1 : (a i).re = r := (Finset.sum_eq_sum_iff_of_le hre).1 hsumre i (Finset.mem_univ i)
  have hsq : ‖a i‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (a i), hle i]
  have hns : ‖a i‖ ^ 2 = (a i).re ^ 2 + (a i).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h3 : (a i).im ^ 2 ≤ 0 := by rw [hns, h1] at hsq; linarith
  have h2 : (a i).im = 0 := sq_eq_zero_iff.1 (le_antisymm h3 (sq_nonneg (a i).im))
  exact Complex.ext (by simpa using h1) (by simpa using h2)

variable {L : Type*} [Group L] [Fintype L] {H Z : Subgroup L}

theorem indClassFun_one (H : Subgroup L) (θ : H → ℂ) :
    indClassFun H θ 1 = (Nat.card H : ℂ)⁻¹ * ∑ _x : L, θ 1 := by
  rw [indClassFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : x⁻¹ * (1 : L) * x = ((1 : H) : L) := by simp
  rw [hx, extendByZero_apply_coe]

theorem indClassFun_apply_of_forall_conj_mem (H : Subgroup L) (θ : H → ℂ) {z : L}
    (hmem : ∀ x : L, x⁻¹ * z * x ∈ H) :
    indClassFun H θ z = (Nat.card H : ℂ)⁻¹ * ∑ x : L, θ ⟨x⁻¹ * z * x, hmem x⟩ := by
  rw [indClassFun_apply]
  congr 1
  exact Finset.sum_congr rfl fun x _ => extendByZero_apply_coe H θ ⟨_, hmem x⟩

omit [Fintype L] in
theorem conj_mem_of_le_of_normal [Z.Normal] (hZH : Z ≤ H) {z : L} (hz : z ∈ Z) (x : L) :
    x⁻¹ * z * x ∈ H :=
  hZH (by simpa using ‹Z.Normal›.conj_mem z hz x⁻¹)

omit [Fintype L] in
theorem conj_mem_subgroupOf_of_normal [Z.Normal] (hZH : Z ≤ H) {z : L} (hz : z ∈ Z) (x : L) :
    (⟨x⁻¹ * z * x, conj_mem_of_le_of_normal hZH hz x⟩ : H) ∈ Z.subgroupOf H := by
  simpa [Subgroup.mem_subgroupOf] using ‹Z.Normal›.conj_mem z hz x⁻¹

theorem subset_charValueKernel_indClassFun_of_subset [Z.Normal] (hZH : Z ≤ H) (θ : H → ℂ)
    (h : (Z.subgroupOf H : Set H) ⊆ charValueKernel θ) :
    (Z : Set L) ⊆ charValueKernel (indClassFun H θ) := by
  intro z hz
  rw [mem_charValueKernel, indClassFun_apply_of_forall_conj_mem H θ
    (conj_mem_of_le_of_normal hZH hz), indClassFun_one]
  congr 1
  exact Finset.sum_congr rfl fun x _ =>
    mem_charValueKernel.1 (h (conj_mem_subgroupOf_of_normal hZH hz x))

theorem subset_charValueKernel_indClassFun_iff [Z.Normal] (hZH : Z ≤ H) {θ : H → ℂ}
    (hθ : θ ∈ irrChars H) :
    (Z : Set L) ⊆ charValueKernel (indClassFun H θ) ↔
      (Z.subgroupOf H : Set H) ⊆ charValueKernel θ := by
  refine ⟨fun h z hz => ?_, subset_charValueKernel_indClassFun_of_subset hZH θ⟩
  obtain ⟨n, hn1, hnle⟩ := exists_degree_of_mem_irrChars hθ
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hz
  have key := h hz
  rw [mem_charValueKernel, indClassFun_apply_of_forall_conj_mem H θ
    (conj_mem_of_le_of_normal hZH hz), indClassFun_one] at key
  have hsum : ∑ x : L, θ ⟨x⁻¹ * (z : L) * x, conj_mem_of_le_of_normal hZH hz x⟩
      = ∑ _x : L, ((n : ℝ) : ℂ) := by
    simpa [hn1] using mul_left_cancel₀ (inv_ne_zero hcard) key
  have h1 := eq_of_norm_le_of_sum_eq (a := fun x : L =>
    θ ⟨x⁻¹ * (z : L) * x, conj_mem_of_le_of_normal hZH hz x⟩) (r := (n : ℝ))
    (fun x => hnle _) hsum 1
  rw [mem_charValueKernel, hn1]
  simpa using h1

theorem forall_indClassFun_eq_one_iff [Z.Normal] (hZH : Z ≤ H) {θ : H → ℂ}
    (hθ : θ ∈ irrChars H) :
    (∀ z ∈ Z, indClassFun H θ z = indClassFun H θ 1) ↔ ∀ z : H, (z : L) ∈ Z → θ z = θ 1 := by
  have h := subset_charValueKernel_indClassFun_iff hZH hθ
  simp only [Set.subset_def, SetLike.mem_coe, mem_charValueKernel, Subgroup.mem_subgroupOf] at h
  exact h

end NormalInduction

end CFSG.FeitThompson
