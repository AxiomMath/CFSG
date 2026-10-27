module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def repP (d : FixData) : ↥P1408 := ⟨elemW d.rep, elemW_mem d.rep⟩

@[expose] def PrimeFacts (p : ℕ) (ds : List FixData) : Prop :=
  (∀ d ∈ ds, Nat.card ↥(P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408)))) =
      d.centOrder ∧ closure (elemW '' {w | w ∈ d.cent}) =
        P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408)))) ∧
    ∀ t : ↥P1408, orderOf t = p → ∃ d ∈ ds, IsConj (repP d) t

structure FixFacts : Prop where
  trans : ∀ q : Fin 1408, ∃ g ∈ P1408, g q = 0
  p3 : Nat.card ↥P1408 = 177408000 → PrimeFacts 3 [fix3]
  p5 : Nat.card ↥P1408 = 177408000 → PrimeFacts 5 [fix5A, fix5B, fix5C]
  p7 : Nat.card ↥P1408 = 177408000 → PrimeFacts 7 [fix7]

end CFSG.EvenSporadicStandard.HNRecog
