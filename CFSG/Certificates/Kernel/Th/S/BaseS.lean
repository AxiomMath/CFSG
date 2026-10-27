module

public import Certificates.Data.CFSGNative.Th.Data

public section

namespace CFSG.KC.Th.BaseS

open CFSG.Sporadic.Th.Native

@[expose] noncomputable def keyRows (l : List Key) : List V4 :=
  List.rec (motive := fun _ => List V4) [] (fun k _ ih => k.u :: k.v :: ih) l

@[expose] noncomputable def deltaRows : List V4 := keyRows deltaKeys.toList

end CFSG.KC.Th.BaseS

end
