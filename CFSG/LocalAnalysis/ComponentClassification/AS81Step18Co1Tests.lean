module

public import CFSG.Sporadic.Co1Block.TwoBData
public import CFSG.Sporadic.Co1Block.IotaBase
public import CFSG.Sporadic.Co1Block.TwoCData

public section

namespace CFSG.ComponentClassification.AS81.Co1Fusion

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block

@[expose] def fusCheckOf (tR : Rows) (d : List (List Int)) (ix ic p k : Nat) : Bool :=
  let D := dag [aR, bR, tR] d
  let x := D.1.getD ix one
  let c := D.1.getD ic one
  let w := pow (mul (mul (mul (pow x (p - 1)) c) x) c) k
  D.2.2 && mul x tR == mul tR x && mul c tR == mul tR c && pow x p == one &&
    CFSG.Sporadic.Co1.InvNative.validRows x && x != one && mul c c == one && mul w w == one &&
    CFSG.Sporadic.Co1.InvNative.validRows w && w != one

@[expose] def fus13Words : List (List Int) :=
  [[19, 23, 23, 43, 35, 39], [44, 44], [15, 15, 39, 19, 7, 19, 39], [46, 46, 46, 46, 46]]

@[expose] def fus11Words : List (List Int) :=
  [[35, 35, 19, 27], [36, 36], [15, 23, 35, 23, 23, 31, 23, 19], [38, 38, 38, 38, 38, 38, 38, 38]]

@[expose] def fus13Check : Bool := fusCheckOf aR (twoBD1 ++ fus13Words) 44 46 13 3

@[expose] def fus11Check : Bool := fusCheckOf iotaCRows (twoCD1 ++ fus11Words) 36 38 11 1

end CFSG.ComponentClassification.AS81.Co1Fusion
