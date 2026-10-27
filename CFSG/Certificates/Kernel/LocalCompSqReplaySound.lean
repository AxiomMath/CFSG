module

public import Certificates.Data.Kernel.LocalComp.Replay
public import Certificates.Data.Kernel.LocalComp.ReplayWit
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.LocalCompSqReplaySnd

public section

namespace CFSG.KC.LocalComp.Replay

open CFSG.KC.LQT CFSG.SectionRank.Native

theorem squareCheck_of_K {c : Lay} {d : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {LA LB : List Char} {V P T O : Nat → Nat} {N : Nat} {D : SqData} {σ : List Nat}
    (hsA : D.seedA = String.ofList LA) (hsB : D.seedB = String.ofList LB)
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hr : replayOK c V P T N D.asData O (fun _ => D.t) = true)
    (hq : sqOK c V N (O 0) (O 1) (O 2) D.r D.oh D.a D.b D.c D.d D.t σ = true) :
    (ops3 d).squareCheck D = true := by
  exact CFSG.KC.LocalComp.SqReplaySnd.squareCheck_main hc hp hd hsA hsB hA hB h1 hs hr hq

end CFSG.KC.LocalComp.Replay

end
