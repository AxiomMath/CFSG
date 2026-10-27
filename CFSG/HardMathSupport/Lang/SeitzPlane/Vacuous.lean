module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.LieType.SeitzGeneration


theorem excPlaneTrialityOddFive : ExcPlaneTrialityOddFive := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨q, rfl⟩, hp5, -⟩ hr
  exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_trialityD4 q hv hp hp5
    (by simpa using hpd))).elim

theorem excPlaneTrialityThree : ExcPlaneTrialityThree := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨q, rfl⟩, rfl⟩ hr
  exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv
    (by simpa [eq_comm] using hpd))).elim

theorem excPlaneReeF4Three : ExcPlaneReeF4Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨m, rfl⟩, rfl⟩ hr
  exact (hr (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)).elim

end CFSG.HardMathSupport.Lang.SeitzPlane
