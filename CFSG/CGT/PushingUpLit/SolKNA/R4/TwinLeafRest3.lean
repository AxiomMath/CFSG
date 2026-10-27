module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafRest2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafM23Holds
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafD43
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafG23

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

structure TwinLeafRest3 : Prop where
  l43 : LocalL43
  u43 : LocalU43
  l53 : LocalL53


theorem twinLeafRest2_of_rest3 (I : TwinLeafRest3) : TwinLeafRest2 :=
  ⟨localG23_holds, localD43_holds, I.l43, I.u43, I.l53, localM23'_holds⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
