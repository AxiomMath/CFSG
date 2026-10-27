module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8Sp6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8O8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

theorem twinQ8Class_proved :
    TwinQ8Class := by
  intro X _ _ hX T₁ T₂ h₁ h₂ hΩ₁ hΩ₂
  rcases hX with hX | hX
  · exact S7Twin.Sp6.sp6_mem_conjClass hX h₁ h₂ hΩ₁ hΩ₂
  · exact S7Twin.O8.o8_mem_conjClass hX h₁ h₂ hΩ₁ hΩ₂

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
