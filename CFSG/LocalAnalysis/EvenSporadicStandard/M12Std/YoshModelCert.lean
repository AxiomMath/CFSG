module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelChecks
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowHom

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

theorem size_nGens (α k : ℕ) : (nGens α k).size = 9 := by
  unfold nGens
  by_cases h : α = 0
  · simp [h, nBase0]
  · simp [h, nBase1]

section Cert


theorem modelFacts_parts :
    (∀ α, α < 2 → sigmaQCheck α = true ∧
      ∀ k, k < 2 → fusionChainsCheck α k = true ∧ fusionCoverCheck α k = true) ∧
    (∀ α k, α < 2 → k < 2 → ueCheck α k = true ∧ esCheck α k = true) ∧
    (∀ k, k < 2 → l6Check 0 k = true) ∧
    (∀ k, k < 2 → l7Check 1 k = true ∧ l8Check 1 k = true) ∧
    sylowHomCheckAll = true := by
  have h : modelFactsCheck = true := by
    have h0 := yoshQ_check
    simp only [yoshQCheck, Bool.and_eq_true] at h0
    exact h0.2
  unfold modelFactsCheck fusionCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun α hα => ?_, fun α k hα hk => ?_, fun k hk => h3 k (by omega),
    fun k hk => h4 k (by omega), h5⟩
  · obtain ⟨h6, h7⟩ := h1 α (by omega)
    exact ⟨h6, fun k hk => h7 k (by omega)⟩
  · exact h2 α (by omega) k (by omega)

theorem modelChecks : ModelChecks where
  fusion α _k hα hk :=
    ⟨hα, size_nGens α _k, nModelOK α _k hα hk, (modelFacts_parts.1 α hα).1,
      ((modelFacts_parts.1 α hα).2 _k hk).1, ((modelFacts_parts.1 α hα).2 _k hk).2⟩
  ue α _k hα hk := (modelFacts_parts.2.1 α _k hα hk).1
  es α _k hα hk := (modelFacts_parts.2.1 α _k hα hk).2
  l6 _k hk := modelFacts_parts.2.2.1 _k hk
  l7 _k hk := (modelFacts_parts.2.2.2.1 _k hk).1
  l8 _k hk := (modelFacts_parts.2.2.2.1 _k hk).2
  sylowHom _k hk := sylowHomCheck_of_all modelFacts_parts.2.2.2.2 hk

end Cert

end CFSG.EvenSporadicStandard.M12Std.Yosh
