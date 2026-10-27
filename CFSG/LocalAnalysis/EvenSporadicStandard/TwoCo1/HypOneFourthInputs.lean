module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Co1Block.TwoBData

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

@[noinline, expose] def fourthRootCheckOf (tR : Rows) (d₁ : List (List Int)) (bidx : List Nat)
    (d₂ : List (List Int)) (sIdx : List Nat) (ord : Nat) : Bool :=
  let D₁ := brayRows tR d₁
  let B := brayElts D₁ bidx
  let D₂ := dag B d₂
  let sg : Array Rows := (sIdx.map fun j => D₂.1.getD j one).toArray
  let T := gtBFS sg (ord + 1)
  D₁.2.2 && D₂.2.2 && B.all (fun g => mul g tR == mul tR g && mul g (inv g) == one) &&
    gtOK sg T && T.pts.size == ord && validRows tR &&
    T.pts.all (fun p => mul (mul p p) (mul p p) != tR)

@[expose] def fourthRootCheckB : Bool :=
  fourthRootCheckOf aR twoBD1 twoBBray sylD2B sylIdxB 32768

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
