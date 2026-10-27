module

public import CFSG.Certificates.Kernel.KDenseP.CM12.Run
public import CFSG.Certificates.Kernel.KDenseP.CM12.Pairs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenInputs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.CM12 CFSG.HardMathSupport.Dickson.BMRows.M11 in
@[expose] noncomputable def CFSG.KD.CM12.c17702.run := CFSG.KD.CM12.runP (tri m12Pairs n17702)

#kc_chain CFSG.KD.CM12.c17702 CFSG.KD.CM12.c17702.run "c17702.plan.txt" 3498 12255992164023254090
#kc_select CFSG.KD.CM12.c17702 Xf X 76
#kc_select CFSG.KD.CM12.c17702 Af A 76
#kc_select CFSG.KD.CM12.c17702 Wf W 76
#kc_select CFSG.KD.CM12.c17702 CH CH 98

namespace CFSG.KD.CM12.c17702

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.CM12
  CFSG.HardMathSupport.Dickson.BMRows.M11

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri m12Pairs n17702) S (CH k)

end CFSG.KD.CM12.c17702

#kc_each CFSG.KD.CM12.c17702.t 0 98

end
