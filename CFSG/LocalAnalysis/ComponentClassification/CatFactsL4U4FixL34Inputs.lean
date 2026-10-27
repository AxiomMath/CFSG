module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.PSL3Four.Native

@[expose] def sqT (y : Tab) : Tab := comp 42 y y

@[expose] def pow256T (y : Tab) : Tab := sqT (sqT (sqT (sqT (sqT (sqT (sqT (sqT y)))))))

@[expose] def commT (y x : Tab) : Bool := comp 42 y x == comp 42 x y

@[expose, noinline] def fixCheck (ER C : Array Tab) (r : Tab) : Bool :=
  allBelow ER.size fun k =>
    !(commT ER[k]! r) || !(C.all fun c => commT ER[k]! c) || !(pow256T ER[k]! == idTab 42) ||
      ER[k]! == idTab 42 || ER[k]! == r

end CFSG.ComponentClassification.CatFactsL4U4
