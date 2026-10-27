module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {X : Type} [Group X]

theorem isFaithfulL3E8_of_two_q8 (hX : IsL3E8 X) {P P' : Subgroup X} {z z' : X}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hz : IsUniqueInvolution P z)
    (hP' : Nonempty (↥P' ≃* QuaternionGroup 2)) (hz' : IsUniqueInvolution P' z') (hne : z ≠ z') :
    IsFaithfulL3E8 X := by
  obtain ⟨E, hEn, hEab, hcard, ⟨e⟩⟩ := hX
  rcases l3e8_centralizer_dichotomy hEab e with h | h
  · exact ⟨E, ⟨hEn, hEab, hcard, h, ⟨e⟩⟩⟩
  · exact absurd (l3e8_central_q8_involution_eq hEab h e hP hz hP' hz') hne

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
