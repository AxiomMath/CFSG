module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open CFSG.PSL3Four.Native

@[expose] def hfi34Check (ER O₃ : Array Tab) : Bool :=
  let C := centTabs 42 ER r₃T
  allBelow C.size fun k =>
    !(comp 42 C[k]! C[k]! == idTab 42 && !(C[k]! == idTab 42) && !(C[k]! == r₃T)) ||
      !(memTab O₃ C[k]!) || !(memTab O₃ (comp 42 r₃T C[k]!))

end CFSG.EvenSporadicStandard.HSStd.HFI
