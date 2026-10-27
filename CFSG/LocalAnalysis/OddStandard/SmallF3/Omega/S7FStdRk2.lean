module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFrontierFinal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdDefs
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint


theorem asc82StandardInputRk2_holds : Asc82StandardInputRk2 := by
  intro G _ _ hs hK hn _ _ _ X hX hXF hrk
  haveI := hs
  have hnonab : ∃ a b : G, a * b ≠ b * a :=
    s7f_nonab_of_quasisimple (s7f_isQuasisimple_of_inFStar hXF)
  have hrk' : 2 ≤ CFSG.Open.pRank 2 (centralizer (X : Set G)) := by
    rwa [← CFSG.SectionRank.pRank_coe_eq_openPRank]
  exfalso
  apply hn
  rcases CFSG.ComponentClassification.RankTwoStandard.ct_rank_two_standard_recognition_models
      G hnonab hK X hX hrk' with ⟨n, hn9, he⟩ | h
  · exact Or.inr (Or.inl ⟨n, by omega, he⟩)
  · rcases h with h | h | h | h | h <;> exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))

end CFSG.OddStandard.SmallF3.Omega
