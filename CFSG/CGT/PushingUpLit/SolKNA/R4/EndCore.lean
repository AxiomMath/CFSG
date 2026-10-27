module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Core
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EndGold

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

section Gold


theorem tightC19_11bSR_of_F1 {r : ℕ} (hF1 : TightF1SR r) : TightC19_11bSR r :=
  tightC19_11bSR_of_F1_endgame hF1 tightEndGameSR_holds

end Gold

end CFSG.CGT.PushingUpLit.SolKNA.R4
