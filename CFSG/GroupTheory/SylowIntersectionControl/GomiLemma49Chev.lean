module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Reduction
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GroupTheory

open CFSG.QuasithinUnique.Bridge CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem gomiLemma49Chev_holds :
    GomiLemma49Chev := by
  intro G _ _ hs h
  have hAut := (CFSG.Quasithin.LieOver.asLieTwo_holds).2
  have hLie : ∀ {t : CFSG.Open.StatedLieTag} {n f : ℕ}, CFSG.Blueprint.LieModel G t n 2 f →
      SylowAutTrivial G := fun hL => hAut G hs (Or.inl ⟨_, _, _, hL.admissible, hL⟩)
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨i, hv⟩, hi, ⟨e⟩⟩
  · have hc : d.1.characteristic = 2 := by
      have key : ∀ i : TauCeti.LieTypeIndex, IsChevIndexTwo i → i.characteristic = 2 := by
        intro i hi
        cases i <;> simp_all [IsChevIndexTwo]
      exact key d.1 hd
    obtain ⟨t, m, f, hL⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hc e
    exact hLie hL
  · exact sylowAutTrivial_alt hn e
  · obtain ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ := hi
    · simp only at hiq
      subst hiq
      exact hLie (CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e)
    · simp only at hiq
      subst hiq
      exact hAut G hs (Or.inr
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e))

end CFSG.GroupTheory

end
