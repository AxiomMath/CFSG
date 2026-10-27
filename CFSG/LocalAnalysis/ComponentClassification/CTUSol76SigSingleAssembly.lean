module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleOddB
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleAlt

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem singleComponentQuasisimpleAt_or {P Q : (S : Type) → [Group S] → Prop}
    (hP : SingleComponentQuasisimpleAt P) (hQ : SingleComponentQuasisimpleAt Q) :
    SingleComponentQuasisimpleAt (fun S _ => P S ∨ Q S) := by
  intro R _ _ hR hO hPQ
  rcases hPQ with h | h
  · exact hP R hR hO h
  · exact hQ R hR hO h

theorem singleComponentQuasisimpleAt_of_imp {P Q : (S : Type) → [Group S] → Prop}
    (h : SingleComponentQuasisimpleAt P) (hQP : ∀ (S : Type) [Group S], Q S → P S) :
    SingleComponentQuasisimpleAt Q := by
  intro R _ _ hR hO hQ
  exact h R hR hO (hQP _ hQ)

section Certified


theorem singleComponentQuasisimpleAt_classicalRep_of_clean
    (h : SingleComponentCleanAt (fun S _ => OddClassicalRep S)) :
    SingleComponentQuasisimpleAt (fun S _ => Milestones.ClassicalRep S) :=
  singleComponentQuasisimpleAt_of_imp (singleComponentQuasisimpleAt_or
      (singleComponentQuasisimpleAt_of_simpleAt singleComponentSimpleAt_classical_even)
      (singleComponentQuasisimpleAt_classical_of_clean h))
    fun _ _ h => classicalRep_even_or_odd h


theorem singleComponentQuasisimpleAt_exceptionalRep_of_clean
    (h : SingleComponentCleanAt (fun S _ => OddExceptionalRep S)) :
    SingleComponentQuasisimpleAt (fun S _ => Blueprint.ExceptionalRep S) :=
  singleComponentQuasisimpleAt_of_imp (singleComponentQuasisimpleAt_or
      (singleComponentQuasisimpleAt_of_simpleAt singleComponentSimpleAt_exceptional_even)
      (singleComponentQuasisimpleAt_exceptional_of_clean h))
    fun _ _ h => exceptionalRep_even_or_odd h

theorem singleComponentQuasisimpleFor_of_clean
    (hC : SingleComponentCleanAt (fun S _ => OddClassicalRep S))
    (hE : SingleComponentCleanAt (fun S _ => OddExceptionalRep S))
    (hS : SingleComponentQuasisimpleAt (fun S _ => Blueprint.NativeSporadic.SporadicRep S)) :
    SingleComponentQuasisimpleFor :=
  singleComponentQuasisimpleFor_of_families singleComponentQuasisimpleAt_alternating
    (singleComponentQuasisimpleAt_classicalRep_of_clean hC)
    (singleComponentQuasisimpleAt_exceptionalRep_of_clean hE) hS

end Certified

end CFSG.ComponentClassification.Sol76.Sig
