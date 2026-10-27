module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinMainR
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL43
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL53
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

theorem twinMainInputsR_holds :
    TwinMainInputsR :=
  ⟨⟨TwinLeaf.localL43_holds, TwinLeaf.localU43_holds, TwinLeaf.localL53_holds⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
