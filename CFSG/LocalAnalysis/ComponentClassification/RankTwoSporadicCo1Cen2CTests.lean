module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PWTests
public import CFSG.Sporadic.Co1Block.TwoCCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative

@[expose] def co1Cen2CBase : List Rows := aR :: bR :: iotaCRows :: twoCQRows

@[noinline, expose] def co1QcScanOK (pts : Array Rows) (c : Rows) (S : List Rows) : Bool :=
  S.all validRows && pts.all fun r =>
    validRows r && (r == one || r == c || S.any fun s => !commR r s)

@[expose] def co1Cen2CCheck (glob : List (List Nat)) (s₁ s₂ : List Nat)
    (d₁ d₂ : List (List Nat)) (zh₁ zh₂ : Nat × Nat) (dec₁ dec₂ : List (List Nat))
    (rd : List (List Nat)) (re : List Nat) : Bool :=
  (dag co1Cen2CBase (glob.map decWord)).2.2 &&
    pwOK (entriesR co1Cen2CBase (glob.map decWord) s₁) (d₁.map decWord) zh₁.1 zh₁.2 dec₁
      iotaCRows &&
    pwOK (entriesR co1Cen2CBase (glob.map decWord) s₂) (d₂.map decWord) zh₂.1 zh₂.2 dec₂
      iotaCRows &&
    wordsOK (entriesR co1Cen2CBase (glob.map decWord) s₁ ++
      entriesR co1Cen2CBase (glob.map decWord) s₂) (rd.map decWord) re twoCRoots &&
    co1QcScanOK (gtBFS twoCQRows.toArray 2048).pts iotaCRows
      (entriesR co1Cen2CBase (glob.map decWord) s₁ ++
        entriesR co1Cen2CBase (glob.map decWord) s₂)

end CFSG.ComponentClassification.RankTwoSporadic.Co1
