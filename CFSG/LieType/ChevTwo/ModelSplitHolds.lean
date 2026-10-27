module

public import CFSG.LieType.ChevTwo.ModelSplit
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LieType.ChevTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

private theorem characteristic_two_of_isChevIndexTwo {i : TauCeti.LieTypeIndex}
    (h : IsChevIndexTwo i) : i.characteristic = 2 := by
  cases i <;> simp_all [IsChevIndexTwo]

theorem chevTwoModelSplit_holds :
    ChevTwoModelSplit := by
  intro K _ h
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨i, hv⟩, hi, ⟨e⟩⟩
  · obtain ⟨t, m, f, hL⟩ :=
      CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d
        (characteristic_two_of_isChevIndexTwo hd) e
    by_cases ht : t = .Tits
    · subst ht
      exact Or.inr (Or.inl ⟨m, f, hL⟩)
    · exact Or.inl ⟨t, m, f, ht, hL⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl ⟨.PSL, 2, 2, by decide,
        CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e⟩
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    · exact Or.inl ⟨.PSL, 4, 1, by decide,
        CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e⟩
  · obtain ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ := hi
    · simp only at hiq
      subst hiq
      exact Or.inl ⟨.PSL, 3, 1, by decide,
        CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e⟩
    · simp only at hiq
      subst hiq
      exact Or.inr (Or.inr (Or.inr
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two
          q hv hq e)))

end CFSG.LieType.ChevTwo
