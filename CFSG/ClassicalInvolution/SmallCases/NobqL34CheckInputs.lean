module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def cqTab (c g gi : Tab) : Tab := comp 42 c (comp 42 (comp 42 g c) gi)

@[expose] def cqTabCheck (C Ci : Array Tab) (r : Tab) : Bool :=
  invsOK 42 C Ci &&
    allBelow C.size fun a =>
      !(comp 42 C[a]! C[a]! == r) ||
        anyBelow C.size fun b =>
          comp 42 (cqTab C[a]! C[b]! Ci[b]!) (cqTab C[a]! C[b]! Ci[b]!) == idTab 42 &&
            !(cqTab C[a]! C[b]! Ci[b]! == idTab 42) && !(cqTab C[a]! C[b]! Ci[b]! == r)

@[expose] def keyTabCheck (ER C : Array Tab) (r : Tab) : Bool :=
  allBelow ER.size fun k =>
    !(comp 42 ER[k]! ER[k]! == r) ||
      anyBelow C.size fun j =>
        !(comp 42 ER[k]! C[j]! == comp 42 C[j]! ER[k]!) &&
          !(comp 42 ER[k]! C[j]! == comp 42 (comp 42 r C[j]!) ER[k]!)

@[expose] def l34C : Array Tab := centTabs 42 (enumBFS 42 gensS 20160).tabs r₁T

@[expose] def l34CQ : Bool := cqTabCheck l34C (l34C.map (invTab 42)) r₁T

@[expose] def l34Key : Bool := keyTabCheck (enumBFS 42 gTabs 241920).tabs l34C r₁T

end CFSG.ClassicalInvolution.Nobq
