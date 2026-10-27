module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint

theorem evenPumpSpor_B :
    EvenPumpSporClauseFor .B :=
  evenPumpSporClauseFor_of_comps BMCase.sporadicOddCoreFree_B
    (fun _ _ _ _ _ ⟨e⟩ t ht K hK => by
      obtain ⟨-, hiso, -⟩ :=
        Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
          K hK
      rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 76532479683774853939200)
          (factorial_div_two_ne_even 24 (by decide) (by decide))
          (by rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup])
      · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
        exact noEvenAltBelow_of_card_quotient_center_eq (c := 3311126603366400)
          (factorial_div_two_ne_even 19 (by decide) (by decide))
          (by rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
            Monster.B.E6.FieldInvF4.card_groupJ]))
    (outer_noEvenAlt_of_forall_inner
      (BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B ⟨MulEquiv.refl NativeSporadic.B⟩))

end CFSG.ComponentClassification.EvenPump
