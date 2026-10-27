module

public import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply)

@[expose] def d8WitnessOK : Bool :=
  qmul gArr 2 2 == 0 && qmul gArr 32 32 == 0 && qmul gArr 2 1 == qmul gArr 1 2 &&
    qmul gArr 32 1 == qmul gArr 1 32 &&
    qmul gArr (qmul gArr 2 32) (qmul gArr 2 32) == 2 ^ 22 &&
    qmul gArr (qmul gArr 1 2) (qmul gArr 1 2) == 0 &&
    qmul gArr (qmul gArr 1 32) (qmul gArr 1 32) == 0 &&
    qmul gArr 9 9 == 0 && qmul gArr 3162 3162 == 0 &&
    qmul gArr 3162 128 == qmul gArr 128 3162 &&
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsN 8).toArray 3162) 3162) ==
      5449715 &&
    qmul gArr 2 1255411 == qmul gArr (qmul gArr 1255411 2) (2 ^ 22) &&
    qmul gArr (qmul gArr 128 2) (qmul gArr 128 2) == 0 &&
    qmul gArr (qmul gArr 128 9) (qmul gArr 128 9) == 0 &&
    qmul gArr (qmul gArr 128 3162) (qmul gArr 128 3162) == 0 &&
    qmul gArr 1255411 (2 ^ 22) == 5449715

end CFSG.EvenSmallLie.TwoE6
