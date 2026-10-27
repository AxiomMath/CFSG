module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public import CFSG.Sporadic.Co1Block.TwoCCheckInputs
public import CFSG.Sporadic.Co1Block.TwoBData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoCData
public meta import CFSG.Sporadic.Co1Block.TwoACheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoCCheckInputs
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

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

@[expose] def fourRows (X : Rows) : Bool :=
  mul (mul X X) (mul X X) == one && mul X X != one

@[noinline, expose] def sylowCheckOf (tR : Rows) (d₁ : List (List Int)) (bidx : List Nat)
    (d₂ : List (List Int)) (sIdx : List Nat) (ord : Nat) : Bool :=
  let D₁ := brayRows tR d₁
  let B := brayElts D₁ bidx
  let D₂ := dag B d₂
  let sg : Array Rows := (sIdx.map fun j => D₂.1.getD j one).toArray
  let cg : Array Rows := B.toArray
  let T := gtBFS sg (ord + 1)
  D₁.2.2 && D₂.2.2 && B.all (fun g => mul g tR == mul tR g && mul g (inv g) == one) &&
    gtOK sg T && T.pts.size == ord &&
    T.pts.all (fun p => !fourRows p || conjAtLeast cg (cg.map inv) p 5)

@[expose] def pickRows (D : List Rows × List Rows × Bool) (idx : List Nat) : List Rows :=
  idx.map fun j => D.1.getD j one

@[expose] def commRows (D : List Rows × List Rows × Bool) (cIdx : List (Nat × Nat)) : List Rows :=
  cIdx.map fun ij =>
    mul (mul (inv (D.1.getD ij.1 one)) (inv (D.1.getD ij.2 one)))
      (mul (D.1.getD ij.1 one) (D.1.getD ij.2 one))

@[noinline, expose] def perfectCheckOf (B : List Rows) (dP : List (List Int)) (pIdx : List Nat)
    (dU : List (List Int)) (cIdx : List (Nat × Nat)) (dF : List (List Int)) (fIdx : List Nat)
    (dQ : List (List Int)) (qIdx : List Nat) (Qr : List Rows) : Bool :=
  let DP := dag B dP
  let P := pickRows DP pIdx
  let DU := dag P dU
  let C := commRows DU cIdx
  let DF := dag C dF
  let DQ := dag P dQ
  DP.2.2 && DU.2.2 && DF.2.2 && DQ.2.2 &&
    cIdx.all (fun ij => mul (DU.1.getD ij.1 one) (inv (DU.1.getD ij.1 one)) == one &&
      mul (DU.1.getD ij.2 one) (inv (DU.1.getD ij.2 one)) == one) &&
    pickRows DF fIdx == P && pickRows DQ qIdx == Qr

@[expose] def perfectCheckA : Bool :=
  perfectCheckOf (brayElts (brayRows iotaARows twoAD1) twoABray) perfPA perfPIdxA perfUA perfCIdxA
    perfFA perfFIdxA perfQA perfQIdxA twoAQRows

@[expose] def sylowCheckB : Bool :=
  sylowCheckOf aR twoBD1 twoBBray sylD2B sylIdxB 32768

@[expose] def perfectCheckC : Bool :=
  perfectCheckOf (brayElts (brayRows iotaCRows twoCD1) twoCBray) perfPC perfPIdxC perfUC perfCIdxC
    perfFC perfFIdxC perfQC perfQIdxC twoCQRows

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
