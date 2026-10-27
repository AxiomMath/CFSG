module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup

theorem lemma245_C55 : Lemma245_C55 := by
  intro G _ _ T M H S L hcs M₀ hSM hMT hne _
  exact C56.c55 hcs hSM hMT hne

theorem lemma245_C56_7 (hA5 : C56A5Case) (hD : C56DoubleCase) : Lemma245_C56_7 := by
  rw [lemma245_C56_7_iff]
  intro G _ _ T M H S L hcs M₀ hSM hMT h2
  by_cases hj : conjJoin S L = L
  · by_cases h5 : IsAltType L 5
    · exact hA5 G T M H S L hcs h5 hj M₀ hSM hMT h2
    · have hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3 := by
        rcases hcs.block.2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h5
      exact C56.c56_7_single naturalModuleStructure hcs hj hL h5 hSM hMT h2
  · exact hD G T M H S L hcs hj M₀ hSM hMT h2

theorem lemma245_4 (h : Lemma245_C56_7) : Lemma245_4 := by
  intro G _ _ T M H S L hcs
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  exact (h G T M H S L hcs M₀ hSM hMT h2).1

end CFSG.QuasithinUnique
