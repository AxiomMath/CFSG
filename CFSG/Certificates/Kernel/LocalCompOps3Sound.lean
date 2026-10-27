module

public import Certificates.Data.Kernel.LocalComp.Replay
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.LocalCompOps3Snd.Replay

public section

namespace CFSG.KC.LocalComp.Replay

open CFSG.KC.LQT CFSG.SectionRank.Native

theorem ops3_check_of_K {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {V P T O W : Nat → Nat} {N : Nat} {D : Data}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : replayOK c V P T N D O W = true)
    (he : elemOK c V N O W D.outs.length = true) :
    (ops3 d).check D = true := by
  exact CFSG.KC.LocalComp.Ops3Snd.ops3_check_main hc hp hd hsA hsB hA hB h1 hs hr he

end CFSG.KC.LocalComp.Replay

end
