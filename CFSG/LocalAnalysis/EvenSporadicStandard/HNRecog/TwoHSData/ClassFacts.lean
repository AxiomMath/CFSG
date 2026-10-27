module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

structure ClassSpec (r : WClass) (t : Equiv.Perm (Fin 1408)) : Prop where
  class_ncard : (CFSG.Sporadic.SmallOddCore.conjClass P1408 t).ncard = r.classSize
  cent_card : Nat.card ↥(P1408 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) = r.centOrder
  cent_eq : closure (elemW '' {w | w ∈ r.centGens}) =
    P1408 ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 1408)))

end CFSG.EvenSporadicStandard.HNRecog
