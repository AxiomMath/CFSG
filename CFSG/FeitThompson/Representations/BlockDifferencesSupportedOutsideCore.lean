module

public import CFSG.FeitThompson.Representations.FrobeniusTypeLocalBlockData
import CFSG.FeitThompson.Representations.SignedPairInducedBlockSpans
import CFSG.FeitThompson.Representations.DegreeZeroVirtualCharactersNormTwo

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexOrder

variable {L : Type*} [Group L]

def coreCentralizerSupportOutsideCore (H : Subgroup L) : Set L :=
  coreCentralizerSupport H \ ((H : Set L) \ {1})

theorem mem_coreCentralizerSupportOutsideCore {H : Subgroup L} {x : L} :
    x ∈ coreCentralizerSupportOutsideCore H ↔
      x ∈ coreCentralizerSupport H ∧ x ∉ (H : Set L) \ {1} := Iff.rfl

theorem coreCentralizerSupportOutsideCore_subset (H : Subgroup L) :
    coreCentralizerSupportOutsideCore H ⊆ coreCentralizerSupport H := Set.sdiff_subset

theorem mem_coreCentralizerSupportOutsideCore_iff {H : Subgroup L} {x : L} :
    x ∈ coreCentralizerSupportOutsideCore H ↔ x ∈ coreCentralizerSupport H ∧ x ∉ H :=
  ⟨fun hx => ⟨hx.1, fun hxH => hx.2 ⟨hxH, (mem_coreCentralizerSupport.1 hx.1).1⟩⟩,
    fun hx => ⟨hx.1, fun h => hx.2 h.1⟩⟩

theorem coreCentralizerSupportOutsideCore_eq_diff (H : Subgroup L) :
    coreCentralizerSupportOutsideCore H = coreCentralizerSupport H \ (H : Set L) := by
  ext x; simpa using mem_coreCentralizerSupportOutsideCore_iff

theorem one_notMem_coreCentralizerSupportOutsideCore (H : Subgroup L) :
    (1 : L) ∉ coreCentralizerSupportOutsideCore H := fun h =>
  (mem_coreCentralizerSupport.1 h.1).1 rfl

theorem coreCentralizerSupportOutsideCore_bot :
    coreCentralizerSupportOutsideCore (⊥ : Subgroup L) = ∅ := by
  rw [coreCentralizerSupportOutsideCore, coreCentralizerSupport_bot, Set.empty_sdiff]

variable {H U U₁ : Subgroup L} [H.Normal] [Fintype L]

theorem support_sub_subset_coreCentralizerSupportOutsideCore
    (hD : IsFrobeniusTypeLocalData H U U₁) {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    Function.support (χ - ψ) ⊆ coreCentralizerSupportOutsideCore H := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  refine Function.support_subset_iff'.2 fun x hx => ?_
  rw [Pi.sub_apply, sub_eq_zero]
  rw [mem_coreCentralizerSupportOutsideCore_iff] at hx
  push Not at hx
  by_cases hxA : x ∈ coreCentralizerSupport H
  ·
    have := congrFun (resClassFun_eq_of_mem_irrConstituents hD hlam hχ hψ) ⟨x, hx hxA⟩
    rwa [resClassFun_apply, resClassFun_apply] at this
  · by_cases hx1 : x = 1
    ·
      subst hx1
      rw [apply_one_of_mem_irrConstituents hD hlam hχ,
        apply_one_of_mem_irrConstituents hD hlam hψ]
    ·
      have hxn : x ∉ insert (1 : L) (coreCentralizerSupport H) := by
        simp only [Set.mem_insert_iff]
        exact fun h => h.elim hx1 fun h => hxA h
      rw [eq_zero_of_notMem_insert_one_coreCentralizerSupport
          (irrConstituents_subset_irrDetect H hθ hχ) hxn,
        eq_zero_of_notMem_insert_one_coreCentralizerSupport
          (irrConstituents_subset_irrDetect H hθ hψ) hxn]

theorem sub_apply_one_eq_zero_of_mem_irrConstituents
    (hD : IsFrobeniusTypeLocalData H U U₁) {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    (χ - ψ) 1 = 0 := by
  obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
  rw [Pi.sub_apply, apply_one_of_mem_irrConstituents hD hlam hχ,
    apply_one_of_mem_irrConstituents hD hlam hψ, sub_self]

theorem cfInner_sub_self_eq_two_of_mem_irrConstituents {θ χ ψ : L → ℂ}
    (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) (hne : χ ≠ ψ) :
    cfInner (χ - ψ) (χ - ψ) = 2 :=
  cfInner_self_sub_of_mem_Irr (mem_irrConstituents.1 hχ).1 (mem_irrConstituents.1 hψ).1 hne

theorem coreCentralizerSupportOutsideCore_nonempty (hD : IsFrobeniusTypeLocalData H U U₁)
    {θ : L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) (hne : χ ≠ ψ) :
    (coreCentralizerSupportOutsideCore H).Nonempty := by
  rcases Set.eq_empty_or_nonempty (coreCentralizerSupportOutsideCore H) with hemp | h
  · have hz : χ - ψ = 0 := by
      have hs := support_sub_subset_coreCentralizerSupportOutsideCore hD hθ hχ hψ
      rw [hemp, Set.subset_empty_iff, Function.support_eq_empty_iff] at hs
      exact hs
    have h2 := cfInner_sub_self_eq_two_of_mem_irrConstituents hχ hψ hne
    rw [hz, cfInner_zero_left] at h2
    exact absurd h2 (by norm_num)
  · exact h

theorem isFrobeniusTypeLocalData_sub_irrConstituents_facts
    (hD : IsFrobeniusTypeLocalData H U U₁) {θ : L → ℂ}
    (hθ : θ ∈ indFam H (nonprincipalIrr H))
    {χ ψ : L → ℂ} (hχ : χ ∈ irrConstituents θ) (hψ : ψ ∈ irrConstituents θ) :
    Function.support (χ - ψ) ⊆ coreCentralizerSupportOutsideCore H ∧ (χ - ψ) 1 = 0 ∧
      (χ ≠ ψ → cfInner (χ - ψ) (χ - ψ) = 2 ∧
        (coreCentralizerSupportOutsideCore H).Nonempty) :=
  ⟨support_sub_subset_coreCentralizerSupportOutsideCore hD hθ hχ hψ,
    sub_apply_one_eq_zero_of_mem_irrConstituents hD hθ hχ hψ,
    fun hne => ⟨cfInner_sub_self_eq_two_of_mem_irrConstituents hχ hψ hne,
      coreCentralizerSupportOutsideCore_nonempty hD hθ hχ hψ hne⟩⟩

end

end CFSG.FeitThompson
