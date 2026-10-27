module

public import CFSG.Sporadic.Co1Block.TwoCData
public import CFSG.Sporadic.Co1Block.PermData
public import Certificates.Data.CFSGNative.Co1Rank.Dfs
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.TwoCData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import Certificates.Data.CFSGNative.Co1Rank.Dfs
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
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

public section

set_option compiler.extract_closed false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.RankNative

@[expose, irreducible] def rankBD0 : List (List Int) :=
  [
    [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2,
    2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [4, 4, 3, 3, 4, 4,
    3, 4, 3, 3, 4, 4, 3, 4, 4, 3, 3, 3, 3, 4, 4, 3, 3, 3, 4, 4, 4, 3, 4, 3, 3, 4, 4, 3, 4], [5, 5,
    5, 5, 5, 5], [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2,
    2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [1, 2,
    2, 2, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2,
    1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2,
    2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 1], [6, 10, 6, 9], [9, 11, 11, 11, 11, 11], [1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2,
    1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2,
    1, 2], [2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 1], [6, 14, 6, 13], [15, 15, 15, 15, 15, 15], [7, 7, 8, 7, 7, 8, 7, 7, 8, 8, 7,
    8, 7, 8], [8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8,
    8, 7, 7, 8, 8, 8, 8, 8, 7, 7], [6, 18, 6, 17], [19, 19, 19], [7, 7, 7, 8, 7, 7, 7, 7, 7], [7,
    7, 7, 7, 7, 8, 8, 8, 8, 8, 7, 7, 7]]

@[expose, irreducible] def rankBD1 : List (List Int) :=
  [
    [6, 22, 6, 21], [21, 23, 23, 23, 23, 23], [7, 7, 8, 8, 7, 8, 8, 8], [8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7], [6, 26, 6, 25], [27, 27, 27, 27],
    [7, 7, 7, 8, 7, 8, 7, 7, 8, 7, 8, 8, 7, 8, 8, 8, 7, 8, 7, 7, 8, 8, 8, 7, 7], [7, 7, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8,
    8, 8, 8, 7, 7, 7], [6, 30, 6, 29], [29, 31, 31, 31, 31, 31], [8, 7, 8, 7, 7, 8, 7, 7, 8, 8,
    7], [7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8, 8, 8,
    8], [6, 34, 6, 33], [35, 35, 35, 35, 35, 35], [36, 36, 36, 28, 36, 36, 36, 28], [32, 32, 24,
    24, 20, 20], [20, 20, 28, 28, 36, 28, 24, 24], [28, 28, 20], [24, 20, 20, 20, 20, 24, 32],
    [24, 36, 36, 24, 24, 20, 20, 32, 32, 28, 28]]

@[expose, irreducible] def rankBD2 : List (List Int) :=
  [
    [32, 32, 36, 36, 28, 28, 20, 24, 24], [43, 43], [28, 28, 24, 20, 20, 20, 20, 28, 36, 36], [45,
    45], [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12], [-1, -1, 2, -2, 1, 1, -2, 2, -1,
    -1, -2, -2, -2, -1, -1, -1, -2, 1, 1, -1, 1, 2, 1, 2, -2, -2, -2, -2, -2, -1, 2, 1, 1, -1, -2,
    -1, 2, -2, 2, -2, -2, 2, -2, -1, 2, 1, 2, -1, 2, 1, -1, 2, 2, 1, 1, -2, -2, 1, 2, 1], [-2, -1,
    1, 2, -2, -2, 1, 1, 1, -2, 2, 2, -1, 1, 2, 1, 1, 1, 1, -1, -2, 2, 2, -1, 1, 2, 2, 2, -1, -2,
    -2, -2, -2, 1, 2, -2, -1, 2, -2, 2, 2, 2, 1, -2, 2, 1, -2, -1, 1, 2, -2, 2, 2, 2, -2, 1, 1, 1,
    2, 2], [-2, 2, 2, -1, 2, -1, 2, 2, 2, 2, -2, 1, 1, -1, 2, -1, 2, -1, 2, -1, -2, 1, 1, 2, 2,
    -1, -2, -1, 1, 2, -1, -2, 2, -1, 1, 1, -1, 2, -1, 2, 2, 1, 2, -1, -2, 2, 2, -2, 2, -2, 2, -2,
    -2, 1, -2, -1, -1, 1, -2, -2], [-1, 1, -2, 2, 2, -1, 1, 2, 1, -1, 1, 1, -1, -2, 1, 1, -2, 1,
    -1, 2, -1, 1, -2, 1, 1, 2, -1, 2, -2, 1, 2, -1, -1, 1, 1, -1, -1, 2, -1, 1, -2, -2, 1, 2, -1,
    2, -2, 1, -2, 2, 1, 1, -1, 1, 1, 1, 1, -2, 1, 1], [51, 6, -51, 1], [52, 52, 52, 52, 52, 52,
    52, 52, 52, 52], [53, 51], [54, 37, -54], [54, 38, -54], [54, 39, -54], [54, 40, -54], [54,
    41, -54], [54, 42, -54]]

@[expose, irreducible] def rankCLifts : List (List Int) :=
  [
    [1, 3, 2, 1, 5, 2, 5], [8, 3, 3, 6, 2, 5], [2, 5, 8, 6, 2, 3, 8]]

@[expose, irreducible] def rankBD : List (List Int) := rankBD0 ++ rankBD1 ++ rankBD2

@[expose] def rankBIdx : List Nat := [54, 55, 56, 57, 58, 59]

@[expose] def rankBGens : Array (Array Nat) :=
  let D := dag [aR, bR] rankBD
  (rankBIdx.map fun j => D.1.getD j one).toArray

@[expose, irreducible] def rankCD2 : List (List Int) := twoCD2 ++ rankCLifts

@[expose] def rankCIdx : List Nat := twoCQGens ++ [42, 43, 44]

@[expose] def rankCGens : Array (Array Nat) :=
  let D₁ := Native.brayRows iotaCRows twoCD1
  let D₂ := dag (Native.brayElts D₁ twoCBray) rankCD2
  (rankCIdx.map fun j => D₂.1.getD j one).toArray

@[noinline, expose] def rankBCheck (_ : Unit := ()) : Bool :=
  (dag [aR, bR] rankBD).2.2 && rankCheckOf rankBGens 32768 certVecs aR

@[noinline, expose] def rankCCheck (_ : Unit := ()) : Bool :=
  let D₁ := Native.brayRows iotaCRows twoCD1
  D₁.2.2 && (dag (Native.brayElts D₁ twoCBray) rankCD2).2.2 &&
    rankCheckOf rankCGens 262144 certVecs iotaCRows

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
