module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafTwistedG2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3

theorem smallLeafR_twistedG2 {r : ℕ} : SmallLeafR r SmallTwistedG2 :=
  SmallLeafR.of_noDatum4 fun F _ hF => NoDatum4.of_nobq (noDatum_smallTwistedG2 F hF)

end CFSG.CGT.PushingUpLit.SolKNA.R4
