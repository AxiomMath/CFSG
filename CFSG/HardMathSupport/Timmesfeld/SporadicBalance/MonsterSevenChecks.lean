module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenData
public import Certificates.Data.CFSGNative.Timmesfeld.Mon7Check
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  _root_.Timmesfeld.Mon7

@[expose] def Wrho (wo : List ℕ) : List Native.Gen := ((wo.map fun k => wq[k]!).reverse).flatten

@[expose] def pcPairs : List (List Native.Gen × List Native.Gen) :=
  (List.range 6).map (fun i => (powL 7 wq[i]!, ([] : List Native.Gen))) ++
    (List.range 6).flatMap fun i => (List.range 6).filterMap fun j =>
      if i < j then
        some (wq[j]! ++ wq[i]!, wq[i]! ++ Wrho (wordOfVec 6 (cw7[i * 6 + j]!)))
      else none

@[expose] def autPairs : List (List Native.Gen × List Native.Gen) :=
  (List.range 2).flatMap fun a => (List.range 6).map fun i =>
    (wq[i]! ++ autW[a]!, autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!)))

@[expose] def targetW (b : Bool) : List Native.Gen := if b then zW else dW

@[expose] def orbPairs (lo hi : ℕ) : List (List Native.Gen × List Native.Gen) :=
  (List.range' lo (hi - lo)).map fun k =>
    (Wrho orbWord[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!)

@[expose] def ratPairs : List (List Native.Gen × List Native.Gen) :=
  [(dW ++ ratDW, ratDW ++ powL 3 dW), (zW ++ ratZW, ratZW ++ powL 3 zW)]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
