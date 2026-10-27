module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Comps
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint

theorem a10SporClause_B :
    A10SporClauseFor .B :=
  a10SporClauseFor_of_comps BMCase.sporadicOddCoreFree_B
    (fun _ _ _ _ _ ⟨e⟩ t ht K hK => by
      obtain ⟨-, hiso, -⟩ :=
        Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
          K hK
      unfold CompNotA10
      rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
        decide
      · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
        rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
          Monster.B.E6.FieldInvF4.card_groupJ]
        decide)
    (outer_compNotA10_of_forall_inner
      (BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B ⟨MulEquiv.refl NativeSporadic.B⟩))

end CFSG.ComponentClassification.EvenPump
