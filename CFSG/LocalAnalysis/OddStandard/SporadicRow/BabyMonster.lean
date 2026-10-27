module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporDataC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.Generated CFSG.Monster.Existence
open CFSG.Monster.B CFSG.Monster.B.TwoA

theorem sporOddComps_B
    : SporOddComps .B :=
  fun _ _ _ _ _ e t ht B hB _ => by
    obtain ⟨-, hiso, -⟩ :=
      Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
        B hB
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
      exact not_oddLieOrder_E62
    · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        Monster.B.E6.FieldInvF4.card_groupJ]
      exact not_oddLieOrder_F42

theorem sporOddComps_M
    : SporOddComps .M :=
  fun _ _ _ _ _ e t ht B hB _ => by
    rw [card_component_M e t ht B hB]
    exact not_oddLieOrder_B

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
