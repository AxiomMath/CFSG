module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34CertInputs
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit

@[expose] def powTab (t : Tab) : ℕ → Tab
  | 0 => idTab 42
  | n + 1 => comp 42 (powTab t n) t

@[expose] def commT (t s : Tab) : Bool := comp 42 t s == comp 42 s t

@[expose] def topInv (s : Tab) : ℕ → Tab
  | 0 => s
  | n + 1 => if comp 42 s s == idTab 42 then s else topInv (comp 42 s s) n

@[expose] def outSqOK (T S : Array Tab) : Bool :=
  let iS := indexOf S
  allBelow T.size fun k => !(powTwoTab T[k]! 8 == idTab 42) || found iS S (comp 42 T[k]! T[k]!)

@[expose] def centOK (T : Array Tab) (r : Tab) (C : Array Tab) : Bool :=
  allBelow T.size fun k =>
    !(commT T[k]! r && allBelow C.size fun i => commT T[k]! C[i]!) ||
      (T[k]! == idTab 42 || T[k]! == r)

@[expose] def innerOddOK (T C : Array Tab) : Bool :=
  allBelow T.size fun k =>
    !(commT T[k]! r₁T && powTab T[k]! 945 == idTab 42 && !(T[k]! == idTab 42)) ||
      decide (countBelow C.size (fun i => commT T[k]! C[i]!) ≤ 4)

@[expose] def invs₄ (T : Array Tab) : Array Tab :=
  T.filter fun t => commT t r₄T && comp 42 t t == idTab 42 && !(t == idTab 42)

@[expose] def fourOK (T : Array Tab) : Bool :=
  let C := invs₄ T
  allBelow C.size fun i => allBelow C.size fun j =>
    commT C[i]! C[j]! || !(powTwoTab (comp 42 C[i]! C[j]!) 8 == idTab 42) ||
      (comp 42 (topInv (comp 42 C[i]! C[j]!) 8) (topInv (comp 42 C[i]! C[j]!) 8) == idTab 42 &&
        !(topInv (comp 42 C[i]! C[j]!) 8 == idTab 42) &&
        commT (topInv (comp 42 C[i]! C[j]!) 8) C[i]! &&
        !(topInv (comp 42 C[i]! C[j]!) 8 == r₄T) &&
        !(topInv (comp 42 C[i]! C[j]!) 8 == comp 42 r₄T C[i]!) &&
        !(topInv (comp 42 C[i]! C[j]!) 8 == C[i]!))

@[noinline, expose] def rCertOK : Bool :=
  let ER := enumBFS 42 gTabs 241920
  let ES := enumBFS 42 gensS 20160
  outSqOK ER.tabs ES.tabs && centOK ER.tabs r₂T (centTabs 42 ES.tabs r₂T) &&
    centOK ER.tabs r₃T (centTabs 42 ES.tabs r₃T) &&
    innerOddOK ER.tabs (centTabs 42 ES.tabs r₁T) && fourOK ER.tabs

end CFSG.ComponentClassification.GrSLit.L34Facts
