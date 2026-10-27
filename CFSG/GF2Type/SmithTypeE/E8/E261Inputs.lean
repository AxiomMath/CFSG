module

public import CFSG.GF2Type.SmithTypeE.E8.E261
public import CFSG.GF2Type.SmithTypeE.E8.ModSteps
public import CFSG.GF2Type.SmithTypeE.E8.Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

theorem smithE8_steps_of_inputs (hC : SmithE8Compat) (h33 : SmithE8E33) (hF8 : E8ModelFacts)
    (hF : E23FourFacts8) :
    SmithE8E34a ∧ SmithE8E34b ∧ SmithE8E25 ∧ SmithE8LocalInput := by
  have hM : SmithE8Module := smithE8Module_of_model (smithE8Model_of_compat hC)
  obtain ⟨h34a, h34b⟩ := smithE8E34_of h33 (smithE8E34Q_of hF8 hM)
  have h24 := smithE8E24_of hF8 hM
  have h25 := smithE8E25_of hF8 hM
  have h23 := smithE8E23_of hF8 hM
  have h23f := smithE8E23Four_of hF (smithE8Model_of_compat hC) h33 h34a h34b h24
  exact ⟨h34a, h34b, h25, smithE8LocalInput_of h34a h34b h23 h24 h25 h23f⟩

theorem smithE8E261_of_inputs (hC : SmithE8Compat) (h33 : SmithE8E33) (hF8 : E8ModelFacts)
    (hF : E23FourFacts8) : SmithE8E261 := by
  obtain ⟨h34a, h34b, h25, hLoc⟩ := smithE8_steps_of_inputs hC h33 hF8 hF
  exact smithE8E261_of h34a h34b hLoc (smithE8E23a_of h25 h34a h34b hLoc hC) hC h33 hF

end CFSG.GF2Type.SmithTypeE.E8
