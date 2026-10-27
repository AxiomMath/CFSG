module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public import CFSG.Sporadic.Co1Block.TwoBData
public import CFSG.Sporadic.Co1Block.TwoCCheckInputs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

@[expose] def commutesWithAll (B : List Rows) (p : Rows) : Bool :=
  B.all fun g => mul p g == mul g p

@[noinline, expose] def centerFilterOf (tR : Rows) (B : List Rows) (pts : Array Rows) : Bool :=
  B.all validRows && pts.all fun p => !commutesWithAll B p || p == one || p == tR

@[noinline, expose] def centerCheckC : Bool :=
  centerFilterOf iotaCRows (brayElts (brayRows iotaCRows twoCD1) twoCBray)
    (gtBFS twoCQRows.toArray 2048).pts

@[noinline, expose] def centerSylowOf (tR : Rows) (d₁ : List (List Int)) (bidx : List Nat)
    (d₂ : List (List Int)) (sIdx : List Nat) (ord : Nat) : Bool :=
  let B := brayElts (brayRows tR d₁) bidx
  let D₂ := dag B d₂
  let sg : Array Rows := (sIdx.map fun j => D₂.1.getD j one).toArray
  centerFilterOf tR B (gtBFS sg (ord + 1)).pts

@[noinline, expose] def centerCheckB : Bool :=
  centerSylowOf aR twoBD1 twoBBray sylD2B sylIdxB 32768

end CFSG.EvenSporadicStandard.Solomon78
