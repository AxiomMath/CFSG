module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSimple
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem singleComponentSimpleAt_of_noTwoComponent {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T → ∀ x : T, orderOf x = 2 →
      ∀ Q : Subgroup T, ¬ IsTwoComponentIn Q (centralizer ({x} : Set T))) :
    SingleComponentSimpleAt P := by
  intro T _ _ hT hP X Y _ _ _ _ hXr _ _ hcovY _
  obtain ⟨x, hxX, hx2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hXr)
  obtain ⟨Q, -, -, hQ, -⟩ := hcovY x hxX hx2
  exact h T hT hP x hx2 Q hQ

end CFSG.ComponentClassification.Sol76.Sig
