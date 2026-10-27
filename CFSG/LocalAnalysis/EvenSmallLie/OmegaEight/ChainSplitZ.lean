module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitZCheck
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

section Cert


theorem zCheck_parts (ε : Eps) :
    treeCheck ε = true ∧
    (∀ j < 128, mul4 (tilGet ε (zTil ε)) (tilGet ε j) = mul4 (tilGet ε j) (tilGet ε (zTil ε))) ∧
    fix4c (tilGet ε (zTil ε)) = 64 ∧ zTil ε < 128 ∧ zRoot ε < 128 ∧
    mul4 (tilGet ε (zRoot ε)) (tilGet ε (zRoot ε)) = tilGet ε (zTil ε) ∧
    (∀ f ∈ zAnn ε, ∀ n < 4096, dot4 f (mv4 (sub4 one4 (tilGet ε (zTil ε))) (dig4 n)) = 0) ∧
    (∀ w ∈ zWit ε, mv4 (if w.2.2 then add4 one4 (tilGet ε (zRoot ε))
      else sub4 one4 (tilGet ε (zRoot ε))) (dig4 w.2.1) = dig4 w.1) ∧
    ∀ n < 4096, mv4 (add4 one4 (tilGet ε (zTil ε))) (dig4 n) = dig4 0 →
      (∃ w ∈ zWit ε, w.1 = n) ∨ zCount ε n ≤ 128 := by
  have h := zCheck_spec ε
  simp only [zCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun n hn hz => ?_⟩
  rcases h9 n hn with (h | h) | h
  · rw [hz] at h
    simp at h
  · exact Or.inl h
  · exact Or.inr h

theorem tree_facts (ε : Eps) {j : ℕ} (hj : j < 128) (hj0 : j ≠ 0) :
    ∃ i < j, ∃ g < 7, tilGet ε j = mul4 (tilGen ε g) (tilGet ε i) := by
  have h := (zCheck_parts ε).1
  simp only [treeCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := h j' (by omega)
  exact ⟨_, h1, _, h2, h3⟩

end Cert

end CFSG.EvenSmallLie.OmegaEight.Chain
