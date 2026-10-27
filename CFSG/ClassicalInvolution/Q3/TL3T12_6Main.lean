module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6E8
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E64

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

theorem cLeafE8E64_proved (IH : ℕ → Prop) :
    CLeafE8 3 IH ∧ CLeafE64 3 IH :=
  ⟨cLeafE8_of_G (cLeafE8G_proved IH), cLeafE64_of_G (cLeafE64G_proved IH)⟩

end CFSG.ClassicalInvolution.Q3.TC.Thin
