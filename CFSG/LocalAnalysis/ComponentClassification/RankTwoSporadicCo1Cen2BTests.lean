module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PWTests
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Co1.InvNative

@[expose] def co1E2R : Rows := pow (mul twoBXYRows.1 twoBXYRows.2) 13

@[expose] def commRows (u v : Rows) : Rows := mul (mul u v) (mul (inv u) (inv v))

@[noinline, expose] def co1Cen2BTriOK (tab : Array Nat) (T : List (Nat × Nat)) (a e z c : Rows)
    (L : Array Level) (base : Array Nat) : Bool :=
  Native.triOK tab T a && eqA 1365 (Native.triPerm tab T a) (idA 1365) &&
    Native.triOK tab T e && eqA 1365 (Native.triPerm tab T e) (idA 1365) &&
    Native.triOK tab T z &&
    !eqA 1365 (compA 1365 (Native.triPerm tab T z) (Native.triPerm tab T z)) (idA 1365) &&
    Native.triOK tab T c && !siftA 1365 L base 0 (Native.triPerm tab T c)

@[expose] def co1Cen2BMovedOK (H : Array (Array Nat)) : Bool :=
  [1, 5, 83].all fun p => H.any fun h => h[p]! != p

@[expose] def co1Cen2BCheck (hd : List (List Nat)) (uv : Nat × Nat) (cd : List (List Nat))
    (ic : Nat) : Bool :=
  validRows co1E2R && validRows aR && aR != one && mul aR aR == one &&
    mul co1E2R co1E2R == one && co1E2R != one && co1E2R != aR && commR co1E2R aR &&
    commR co1E2R twoBXYRows.1 && commR co1E2R twoBXYRows.2 &&
    (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).2.2 &&
    invsOK (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).1 [uv.1, uv.2] &&
    pow (commRows (entryR (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).1 uv.1)
      (entryR (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).1 uv.2)) 8 == one &&
    (dag [aR, bR] (cd.map decWord)).2.2 && commR (entryR (dag [aR, bR] (cd.map decWord)).1 ic) aR &&
    co1Cen2BTriOK (Native.triTable twoBTris) twoBTris aR co1E2R
      (commRows (entryR (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).1 uv.1)
        (entryR (dag [twoBXYRows.1, twoBXYRows.2] (hd.map decWord)).1 uv.2))
      (entryR (dag [aR, bR] (cd.map decWord)).1 ic)
      (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray &&
    co1Cen2BMovedOK twoBHSteps

end CFSG.ComponentClassification.RankTwoSporadic.Co1
