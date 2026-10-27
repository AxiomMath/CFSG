module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint TauCeti


theorem excPlaneTrialityEvenFive : ExcPlaneTrialityEvenFive := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨q, rfl⟩, hp5, hch⟩ hr
  exfalso
  apply hr
  have hq2 : q.p = 2 := by simpa using hch
  have hmodel := chevalleyModel_cat_trialityD4 hv
  rw [hq2] at hmodel
  have := CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ _ _ _ hmodel
  exact rankLE2_of_noPowThree hp fun _ hE hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_triality_five hmodel hp hp5 hE hc

end CFSG.LieType.SeitzGeneration
