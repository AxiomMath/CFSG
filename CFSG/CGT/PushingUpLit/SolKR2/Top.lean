module

public import CFSG.CGT.PushingUpLit.SolKR2.Facts
public import CFSG.CGT.PushingUpLit.SolKR2.Descent
public import CFSG.CGT.PushingUpLit.SolKR2.FirstHalf
public import CFSG.CGT.PushingUpLit.SolKR2.WeakSig
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

theorem r2First_holds :
    R2First :=
  R2First_of_core CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
    r2Weak_holds
    (r2FirstCore_of CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
      r2Weak_holds)

section Main


theorem solomonTimmesfeldMainRankTwo_holds : SolKAb.SolomonTimmesfeldMainRankTwo :=
  solomonTimmesfeldMainRankTwo_of r2Weak_holds r2First_holds

end Main

end CFSG.CGT.PushingUpLit.SolKR2
