module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open CFSG.PSL3Four.Native

@[expose] def hl34Check (ER O₂ O₄ : Array Tab) : Bool :=
  let C := centTabs 42 ER r₃T
  let W := C.filter fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42
  allBelow C.size fun k =>
    !(comp 42 C[k]! C[k]! == idTab 42 && !(C[k]! == idTab 42) && !(C[k]! == r₃T) &&
        anyBelow W.size fun j => comp 42 W[j]! C[k]! == comp 42 C[k]! W[j]!) ||
      (memTab O₂ C[k]! && memTab O₄ (comp 42 r₃T C[k]!)) ||
      (memTab O₄ C[k]! && memTab O₂ (comp 42 r₃T C[k]!))

end CFSG.EvenSporadicStandard.HSStd.HL34
