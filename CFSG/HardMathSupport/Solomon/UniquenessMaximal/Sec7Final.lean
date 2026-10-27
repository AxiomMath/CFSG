module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Prop71
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L76
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem prop71_of_inputs (i183 : Input18_3_4) (i25 : Input2_5) (i145 : Input14_5)
    (i252 : Input25_2) (i116 : Input11_6) (i18 : Input18_10) (i28 : Input28_8)
    (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B)
    (h63 : ∃ M₀ : Subgroup G, Prop63Out B M₀) (h67 : Prop67Out B) (h68 : Prop68Out B)
    (hU : UniqComp B) : ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M := by
  have h75 := lemma75_of_inputs i183 i25 i145 i252 hS hB h68
  have h76 := lemma76_of_inputs i116 i183 i25 i145 i252 hS hB h68
  exact prop71_of_sec6 hS hB h63 h67 h68 hU h75 h76
    (lemma710_of_inputs hS hB h63 h68 hU h75 h76 i116 lemma23_proved i18 i28)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
