module

public import CFSG.ClassicalInvolution.Asc77.AscT7AAlphaTwin
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

theorem c24_setup : C24_setup p f := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  have hst : AscStand p f Ω K := hs.1.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hKK' : K' ≠ K := hs.1.hne
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hW2 : IsPGroup 2 W := Thompson.isPGroup_of_mem_WSet hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer hΩ hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hWS : W ≤ (S : Subgroup G) := hWT.trans hTS
  have hRS : T ⊓ K ≤ (S : Subgroup G) := inf_le_left.trans hTS
  have hR'S : T ⊓ K' ≤ (S : Subgroup G) := inf_le_left.trans hTS
  obtain ⟨x₁, hx₁, o₁⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hW hWS hK hR hRS hz
  obtain ⟨x₂, hx₂, o₂⟩ := T7C.exists_orderOf_four_mem_inf hp hq hΩ hW hWS hK' hR' hR'S hz'
  have s₁ : x₁ * x₁ = z := T7A.sq_eq_of_orderOf_four hz hx₁.1 o₁
  have s₂ : x₂ * x₂ = z := T7A.sq_eq_of_orderOf_four hz' hx₂.1 o₂
  have hc : x₁ * x₂ = x₂ * x₁ := hWab x₁ hx₁.2 x₂ hx₂.2
  refine ⟨S, T ⊓ K, T ⊓ K', x₁ * x₂, hs, hW, hzW, hS4, hZ, hWS,
    ⟨mem_RSet_of_isSylow2In hK hR, inf_le_right, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', inf_le_right, hR'S⟩,
    Subgroup.mul_mem_sup hx₁.1 hx₂.1, W.mul_mem hx₁.2 hx₂.2, ?_, ?_, ?_⟩
  · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hc]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [s₁, s₂, hz.sq]
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem hx₁.1
  · intro he
    refine T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hx₁.1) hz.mem

end CFSG.ClassicalInvolution.Asc77
