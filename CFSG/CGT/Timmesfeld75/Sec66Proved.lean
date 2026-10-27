module

public import CFSG.CGT.Timmesfeld75.Sec66
public import CFSG.CGT.Timmesfeld75.Sec66Step

public section

namespace CFSG.CGT.Timmesfeld75

theorem sec66ThreeStep_proved (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hA6 : Sec66A6Free) :
    Sec66ThreeStep := fun _ _ _ _ _ _ hc h62 h63 _ _ _ hx hx1 hy h4 hyy hT' hg hfix hyS =>
  hc.sec66_three_step h215 h26 hA6 h62 h63 hx hx1 hy h4 hyy hT' hg hfix hyS

theorem sec66_proved (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hA6 : Sec66A6Free)
    (h62 : Sec62) (h63 : Sec63) : Sec66 :=
  sec66_of_step h62 h63 (sec66ThreeStep_proved h215 h26 hA6)

end CFSG.CGT.Timmesfeld75
