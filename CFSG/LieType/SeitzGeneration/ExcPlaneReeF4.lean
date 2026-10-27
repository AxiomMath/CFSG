module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint TauCeti


theorem excPlaneReeF4Five : ExcPlaneReeF4Five := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨m, rfl⟩, hp5⟩ hr
  exfalso
  apply hr
  have hmodel := reeTitsModel_cat_reeF4 hv
  have := CFSG.LieType.Simplicity.fam_ree_tits_finiteness _ _ _ _ hmodel
  exact rankLE2_of_noPowThree hp fun _ hE hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five hmodel hp hp5 hE hc

end CFSG.LieType.SeitzGeneration
