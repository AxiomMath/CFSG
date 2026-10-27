module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words
public import Certificates.Certificate26770

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem mem_blocks1408_of_preservesHalves {T : Table} {g : Equiv.Perm (Fin 1408)}
    (h : Rep 1408 T g) (hT : preservesHalves T = true) : g ∈ blocks1408 := by
  simp only [preservesHalves, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hT
  rintro ⟨i, hi⟩
  have hgi : ap T i = (g ⟨i, hi⟩).val := by
    rw [h i hi, idx_of_lt g hi, Equiv.Perm.smul_def]
  change (g ⟨i, hi⟩).val < 704 ↔ i < 704
  by_cases h704 : i < 704
  · have := (hT i h704).1
    rw [hgi] at this
    exact ⟨fun _ => h704, fun _ => this⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = 704 + k := ⟨i - 704, by omega⟩
    have := (hT k (by omega)).2
    rw [hgi] at this
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h704⟩

theorem not_mem_blocks1408_of_swapsZero {T : Table} {g : Equiv.Perm (Fin 1408)}
    (h : Rep 1408 T g) (hT : swapsZero T = true) : g ∉ blocks1408 := by
  simp only [swapsZero, decide_eq_true_eq] at hT
  intro hg
  have h0 := hg ⟨0, by norm_num⟩
  have hgi : ap T 0 = (g ⟨0, by norm_num⟩).val := by
    rw [h 0 (by norm_num), idx_of_lt g (by norm_num), Equiv.Perm.smul_def]
  rw [hgi] at hT
  have := h0.2 (by norm_num)
  omega

section Cert


theorem twoHSBasicOK_true : twoHSBasicOK = true := Certificates.certificate26770

private theorem wordA_ok : ∀ l ∈ wordA, 1 ≤ l ∧ l ≤ 7 := by decide
private theorem wordZ_ok : ∀ l ∈ wordZ, 1 ≤ l ∧ l ≤ 7 := by decide
private theorem wordB_ok : ∀ l ∈ wordB, 1 ≤ l ∧ l ≤ 7 := by decide
private theorem wordZ₁_ok : ∀ l ∈ wordZ₁, 1 ≤ l ∧ l ≤ 7 := by decide

theorem rep_elemA : Rep 1408 (tabW wordA) elemA := rep_elemW wordA wordA_ok
theorem rep_elemZ : Rep 1408 (tabW wordZ) elemZ := rep_elemW wordZ wordZ_ok
theorem rep_elemB : Rep 1408 (tabW wordB) elemB := rep_elemW wordB wordB_ok
theorem rep_elemZ₁ : Rep 1408 (tabW wordZ₁) elemZ₁ := rep_elemW wordZ₁ wordZ₁_ok

theorem elemW_wordAZ : elemW wordAZ = elemA * elemZ := by
  simp only [elemW, TwoHS.wordVal, wordAZ, elemA, elemZ, List.map_append, List.prod_append]

theorem rep_elemAZ : Rep 1408 (tabW wordAZ) (elemA * elemZ) := by
  rw [← elemW_wordAZ]
  exact rep_elemW wordAZ (by decide)

theorem twoHSBasic_spec :
    orderOf elemA = 2 ∧ orderOf elemZ = 2 ∧ orderOf elemB = 2 ∧ orderOf elemZ₁ = 2 ∧
      (∀ g ∈ P1408, elemA * g = g * elemA) ∧
      elemA ∈ blocks1408 ∧ elemZ ∈ blocks1408 ∧ elemA * elemZ ∈ blocks1408 ∧
      elemB ∉ blocks1408 ∧ elemZ₁ ∉ blocks1408 := by
  have h := twoHSBasicOK_true
  simp only [twoHSBasicOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hA⟩, hZ⟩, hB⟩, hZ₁⟩, hc⟩, hbA⟩, hbZ⟩, hbAZ⟩, hsB⟩, hsZ₁⟩ := h
  refine ⟨orderOf_eq_two_of_involOK (by norm_num) rep_elemA hA,
    orderOf_eq_two_of_involOK (by norm_num) rep_elemZ hZ,
    orderOf_eq_two_of_involOK (by norm_num) rep_elemB hB,
    orderOf_eq_two_of_involOK (by norm_num) rep_elemZ₁ hZ₁, ?_,
    mem_blocks1408_of_preservesHalves rep_elemA hbA,
    mem_blocks1408_of_preservesHalves rep_elemZ hbZ,
    mem_blocks1408_of_preservesHalves rep_elemAZ hbAZ,
    not_mem_blocks1408_of_swapsZero rep_elemB hsB,
    not_mem_blocks1408_of_swapsZero rep_elemZ₁ hsZ₁⟩
  intro g hg
  rw [← genOf_h1408Gens] at hg
  have hgen : ∀ x ∈ h1408Gens, elemA * tp 1408 x = tp 1408 x * elemA := by
    intro x hx
    exact (commTT_iff rep_elemA (rep_tp (permOK_h1408Gens x hx))).1 (hc x hx)
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact hgen x (by simpa using hx)
  | one => simp
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ hx =>
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hx, ← mul_assoc, inv_mul_cancel, one_mul]

end Cert

end CFSG.EvenSporadicStandard.HNRecog
