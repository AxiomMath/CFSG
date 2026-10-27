module

public import CFSG.Sporadic.Co1Block.TwoCCheckInputs
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.PermData
public import Certificates.Data.Co1HoltFreeTwoC
public meta import CFSG.Sporadic.Co1Block.TwoCCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoCData
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.Co1HoltFreeTwoC

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative

@[expose] def twoCDagRows : List Rows :=
  (dag (Native.brayElts (Native.brayRows iotaCRows twoCD1) twoCBray) twoCD2).1

@[expose] def holtFreePRows : Rows :=
  mul (twoCDagRows.getD Data.pIdx.1 one) (twoCDagRows.getD Data.pIdx.2 one)

@[expose] def holtFreeWRows (q : Rows) : Rows :=
  mul q (mul (mul holtFreePRows q) (pow holtFreePRows 10))

@[expose] def holtFreeA : Rows := holtFreeWRows (twoCQRows.getD Data.aIdx one)

@[expose] def holtFreeB : Rows := holtFreeWRows (twoCQRows.getD Data.bIdx one)

@[expose] def holtFreeF : Rows := holtFreeWRows (twoCQRows.getD Data.fIdx one)

@[noinline, expose] def holtFreeOrderCheck : Bool :=
  pow holtFreePRows 11 == one && holtFreePRows != one && validRows holtFreePRows

@[noinline, expose] def holtFreeFixCheck : Bool :=
  (gtBFS twoCQRows.toArray 2048).pts.all fun r =>
    !(mul holtFreePRows r == mul r holtFreePRows) || r == one || r == iotaCRows

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
