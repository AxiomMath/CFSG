module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Diagonal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.SelfComponent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.OtherComponent

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

section Certified


theorem transferWitness (hKD : KDCo3Cat) (h : CentConfig X a b E Fus) :
    TransferWitness X a Fus := by
  obtain ⟨L, hL, hEL⟩ := h.exists_component_not_commuting
  have ha : orderOf a = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.a_sq) h.a_ne
  have hEC : E ≤ Subgroup.centralizer ({a} : Set X) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.a_comm he)
  rcases component_dichotomy ha hEC h.normal_subgroupOf h.isComponent_E h.le_layer hL hEL with
    ⟨hmoved, hdiag⟩ | ⟨haL, hEL'⟩
  · exact h.case_diagonal hL hmoved hdiag
  · by_cases hEq : E = L
    · subst hEq
      exact h.case_self hL
    · exact h.case_other hKD hL haL hEL' hEq

end Certified

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
