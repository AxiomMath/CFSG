module

public import CFSG.Certificates.Kernel.KDenseP.E11.Run
public import CFSG.Certificates.Kernel.KDenseP.E11.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.E11
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven in
@[expose] noncomputable def CFSG.KD.E11.c16955.run := CFSG.KD.E11.runP (tri elevenPairs n16955)

#kc_chain CFSG.KD.E11.c16955 CFSG.KD.E11.c16955.run "c16955.plan.txt" 3331 17093455905750573240
#kc_select CFSG.KD.E11.c16955 Xf X 62
#kc_select CFSG.KD.E11.c16955 Af A 62
#kc_select CFSG.KD.E11.c16955 Wf W 62
#kc_select CFSG.KD.E11.c16955 CH CH 88

namespace CFSG.KD.E11.c16955

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.E11
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri elevenPairs n16955) S (CH k)

end CFSG.KD.E11.c16955

#kc_each CFSG.KD.E11.c16955.t 0 88

end
