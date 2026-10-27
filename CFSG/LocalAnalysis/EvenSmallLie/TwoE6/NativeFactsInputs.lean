module

public import Mathlib.Data.Nat.Notation
public import Certificates.Data.CFSGNative.CTIB.Coset
meta import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native

@[expose] def fgPairOK (v a : ℕ) : Bool :=
  qmul gArr a 4456968 == qmul gArr 4456968 a &&
    qmul gArr 10541 a == qmul gArr (qmul gArr (autApply gArr (liftImgsN 6).toArray a) 10541) v &&
    qmul gArr 10541 v == qmul gArr (autApply gArr (liftImgsN 6).toArray v) 10541 &&
    qmul gArr v 4456968 == qmul gArr 4456968 v && qmul gArr v v == 0

@[expose] def fgOK : Bool :=
  fgPairOK 5131954 3138877 && fgPairOK 6537621 2916759 && fgPairOK 7180071 7635562 &&
    qmul gArr 5131954 6537621 == 7180071 && qmul gArr 6537621 5131954 == 7180071

end CFSG.EvenSmallLie.TwoE6
