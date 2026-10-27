module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2205
public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap


theorem hyp22Hyp51z_proved : Q3T8.Asc77.Hyp22Hyp51z := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hKΩ : K ∈ Ω := h.stand.mem
  have hK'Ω : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hz : IsUniqueInvolution K z := h.hz
  have hzK' : IsUniqueInvolution K' z := h.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := h.hzK₃
  obtain ⟨h12₁, h12z⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω h.hne.symm hz
    h.hu₁.1 h.hu₂.1 h.hu₂.2
  obtain ⟨h23₁, h23z⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK'Ω hK₃Ω h.hK₃K'.symm hzK'
    h.hu₂.1 h.hu₃.1 h.hu₃.2
  obtain ⟨h13₁, h13z⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK₃Ω h.hK₃K.symm hz
    h.hu₁.1 h.hu₃.1 h.hu₃.2
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) :=
    CFSG.ClassicalInvolution.Asc77.T7B.mem_closure_snd
  have hxB12 : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) :=
    CFSG.ClassicalInvolution.Asc77.T7B.mem_closure_fst
  have hxB23 : u₂ * u₃ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) :=
    CFSG.ClassicalInvolution.Asc77.T7B.mem_closure_thd
  have hxB13 := h.mem_B_13
  have he₁K : u₂ * u₃ ∈ trivialOnQuot K :=
    Subgroup.mul_mem _
      (Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hKΩ h.hne hzK' hz h.hu₂.1)
      (Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK₃Ω hKΩ h.hK₃K hzK₃ hz h.hu₃.1)
  have he₂K' : u₁ * u₃ ∈ trivialOnQuot K' :=
    Subgroup.mul_mem _
      (Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK'Ω h.hne.symm hz hzK' h.hu₁.1)
      (Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK₃Ω hK'Ω h.hK₃K' hzK₃ hzK' h.hu₃.1)
  exact Q3T7P24.hyp51VertexThree_proved h.stand hKΩ hK'Ω hz hzK' h.isElemAbelian_B hzB
    h.hu₁.1 h.hu₂.1 hxB12 h12₁ h12z hxB23 h23₁ h23z he₁K hxB13 h13₁ h13z he₂K'

end CFSG.ClassicalInvolution.Q3.Q3T7
