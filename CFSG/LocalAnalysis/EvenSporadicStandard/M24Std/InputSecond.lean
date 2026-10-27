module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputWreath

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

structure FirstHalfData {G : Type} [Group G] (L : Subgroup G) (z : G) (A B C D : Subgroup G) :
    Prop where
  pair : PairType L A B
  sextet : SextetFacts L A
  octad : OctadBasics L B
  compat : CompatFacts L A B
  trans : TranslationData A z
  cData : CData A z C
  c_elem : ∀ c ∈ C, c * c = 1
  nData : NData B z D

@[expose] def Ega81Lemmas214to217 : Prop :=
  Ega81HypAZ2A8K → HarrisSolomonZ2S6IsoK →
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), KLocalSections G →
      fusionZStar G = ⊥ → standardComponentIsStandard L → LocalSetting G L z →
      ∀ A B C D : Subgroup G, FirstHalfData L z A B C D → WreathData z

end CFSG.EvenSporadicStandard.M24Std
