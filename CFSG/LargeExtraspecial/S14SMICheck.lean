module

public import Certificates.Data.SmithECheck

public section

namespace CFSG.LargeExtraspecial.S14.SMI

open CFSG.SmithE CFSG.F4.Native

@[expose] def commWt (T : Array Nat) : Bool :=
  (List.range 2048).any fun e => isWt (applyCols T e ^^^ e)

@[expose] def chkCommWt : Bool := (List.range 693).all fun k => commWt tvArr[k]!

@[expose] def prodCols (A B : Array Nat) : Array Nat := B.map (applyCols A)

@[expose] def chkProd : Bool :=
  (List.range 693).all fun k => (List.range 693).all fun l => decide (l ≤ k) ||
    hermC uPts[k]! uPts[l]! != 0 || !tvArr.contains (prodCols tvArr[k]! tvArr[l]!)

end CFSG.LargeExtraspecial.S14.SMI
