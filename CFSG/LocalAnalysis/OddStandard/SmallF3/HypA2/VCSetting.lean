module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.FusionDefs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

structure VCSetting {H : Type} [Group H] (M : Subgroup H) (x : H) (T : Subgroup H) (w : H) :
    Prop where
  hM : IsPComponent 2 M
  ox : orderOf x = 2
  hxM : x ∈ normalizer (M : Set H)
  hTM : T ≤ M
  hTx : T ≤ centralizer ({x} : Set H)
  hT : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H)))
  ow : orderOf w = 2
  hwT : w ∈ T
  hwZ : w ∈ (Open.fusionZStar ↥M).map M.subtype

end CFSG.OddStandard.SmallF3.HypA2
