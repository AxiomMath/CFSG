module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLinCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSpCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSUCoverRank

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem ruCoverRank_proved :
    RuCoverRank := by
  intro X _ _ _ hT
  rcases hT with ⟨n, hn, hX⟩ | ⟨m, hm, hX | hX | hX | hX | hX⟩
  · exact three_le_pRank_of_suzukiModel_cover hn hX
  · exact three_le_pRank_of_psp_model_cover hm hX
  · exact three_le_pRank_of_psu_model_cover (Or.inl rfl) hm hX
  · exact three_le_pRank_of_psl_model_cover (by norm_num) hm hX
  · exact three_le_pRank_of_psu_model_cover (Or.inr rfl) hm hX
  · exact three_le_pRank_of_psl_model_cover (by norm_num) hm hX

theorem ruFamilyFacts_proved :
    RuFamilyFacts :=
  ruFamilyFacts_of_coverRank ruCoverRank_proved

end CFSG.EvenSporadicStandard.Induction
