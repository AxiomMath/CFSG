module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

noncomputable abbrev kSub1408 : Subgroup (Equiv.Perm (Fin 1408)) :=
  (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) ⊓ blocks1408

structure TableKFacts : Prop where
  shape : IsShapeK ↥kSub1408
  center : ∀ y ∈ kSub1408, (∀ g ∈ kSub1408, y * g = g * y) →
    y ∈ closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408)))

end CFSG.EvenSporadicStandard.HNRecog

end
