module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6Main
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E29

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

theorem cLeaf126_proved
    (IH : ℕ → Prop) : CLeafE8 3 IH ∧ CLeafE64 3 IH ∧ CLeafE29 3 IH :=
  ⟨(cLeafE8E64_proved IH).1, (cLeafE8E64_proved IH).2, cLeafE29_of_G (cLeafE29G_proved IH)⟩

end CFSG.ClassicalInvolution.Q3.TC.Thin
