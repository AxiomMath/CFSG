module

public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.Timmesfeld.Bridge.Asc72NoPolar

public section

namespace CFSG.CGT.Timmesfeld75

theorem aschbacherNoPolarInput_of_repo :
    AschbacherNoPolarInput := by
  intro G _ _ D hcls hord hodd hgen hrad hdisc hclosed
  obtain ⟨x, hx, y, hy, hxy⟩ := hdisc
  exact CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_of_noPolar ⟨hcls, ⟨hord, hodd⟩, hgen⟩ hrad
    ⟨x, hx, y, hy, fun h => hxy h⟩ hclosed

end CFSG.CGT.Timmesfeld75
