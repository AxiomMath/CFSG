module

public import CFSG.CGT.PushingUpLit.T2KR.P53Setup
public import CFSG.StronglyEmbedded

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

theorem benderSuzukiStatement_holds : BenderSuzukiStatement := fun _ _ _ _ M h =>
  CFSG.Open.fusionIsBenderGroup_of_isBenderGroup (CFSG.BenderSuzuki.bender_suzuki M h)

end CFSG.CGT.PushingUpLit.T2KR.P53
