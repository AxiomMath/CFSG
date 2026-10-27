module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.RestTwistedD
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinusIndex

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding TauCeti

section Main


theorem lieInputRestTwistedD_of_orth_minus (hL : OrthMinusLeviOb) (hC : OrthMinusCentOb) :
    LieInputRestTwistedD := by
  intro Y _ _ d r q hdq hp hR
  obtain ⟨e⟩ := hR
  obtain ⟨i, hv⟩ := d
  have hdq' : i = .twistedD r q := hdq
  subst hdq'
  have hcl : IsClassicalTwoOrG2 Y := Or.inl ⟨⟨_, hv⟩, hp, ⟨e⟩⟩
  exact simpleStmt_of_twistedD_index (d := ⟨.twistedD r q, hv⟩) hL hC hcl rfl hp e

theorem lieInputRest_of_orth_nodes (hLp : OrthPlusLeviOb) (hCp : OrthPlusCentOb)
    (hLm : OrthMinusLeviOb) (hCm : OrthMinusCentOb) : LieInputRest :=
  lieInputRest_of_twistedD_and_orth_plus (lieInputRestTwistedD_of_orth_minus hLm hCm) hLp hCp

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
