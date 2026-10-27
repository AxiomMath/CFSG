module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1PWTests
public import CFSG.Sporadic.Co1Block.IotaBase

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block

@[expose] def co1Cen2AQRows : List Rows :=
  [iotaQRows 0, iotaQRows 1, iotaQRows 2, iotaQRows 3, iotaQRows 4, iotaQRows 5, iotaQRows 6,
    iotaQRows 7]

@[expose] def co1Cen2ABase : List Rows := aR :: bR :: iotaARows :: co1Cen2AQRows

@[expose] def co1Cen2ACheck (glob : List (List Nat)) (s₁ s₂ : List Nat)
    (d₁ d₂ : List (List Nat)) (zh₁ zh₂ : Nat × Nat) (dec₁ dec₂ : List (List Nat))
    (qd : List (List Nat)) (qe : List Nat) : Bool :=
  (dag co1Cen2ABase (glob.map decWord)).2.2 &&
    pwOK (entriesR co1Cen2ABase (glob.map decWord) s₁) (d₁.map decWord) zh₁.1 zh₁.2 dec₁
      iotaARows &&
    pwOK (entriesR co1Cen2ABase (glob.map decWord) s₂) (d₂.map decWord) zh₂.1 zh₂.2 dec₂
      iotaARows &&
    wordsOK (entriesR co1Cen2ABase (glob.map decWord) s₁ ++
      entriesR co1Cen2ABase (glob.map decWord) s₂) (qd.map decWord) qe co1Cen2AQRows

end CFSG.ComponentClassification.RankTwoSporadic.Co1
