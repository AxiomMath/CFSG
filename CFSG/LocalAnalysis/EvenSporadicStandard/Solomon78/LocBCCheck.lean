module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCData
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCData
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.PSL3Four.Native

local notation "RowsT" => CFSG.Sporadic.Co1Schreier.Native.Rows
local notation "rmul" => CFSG.Sporadic.Co1Schreier.Native.mul
local notation "rone" => CFSG.Sporadic.Co1Schreier.Native.one
local notation "rinv" => CFSG.Sporadic.Co1Schreier.Native.inv
local notation "rpow" => CFSG.Sporadic.Co1Schreier.Native.pow
local notation "rword" => CFSG.Sporadic.Co1Schreier.Native.word
local notation "rdag" => CFSG.Sporadic.Co1Schreier.Native.dag
local notation "raR" => CFSG.Sporadic.Co1Schreier.Native.aR
local notation "rbR" => CFSG.Sporadic.Co1Schreier.Native.bR

end CFSG.EvenSporadicStandard.Solomon78
