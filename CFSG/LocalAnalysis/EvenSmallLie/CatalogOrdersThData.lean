module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.SectionRank.Native

@[expose] def prodOrderOK {M V : Type} (O : Ops M V) (sA sB : String) (q k : Nat) : Bool :=
  let X := O.mul (O.decode sA) (O.decode sB)
  O.eq (O.pow X q) O.one && O.vne (O.vmul (O.unit k) X) (O.unit k)

end CFSG.EvenSmallLie.CatalogOrders
