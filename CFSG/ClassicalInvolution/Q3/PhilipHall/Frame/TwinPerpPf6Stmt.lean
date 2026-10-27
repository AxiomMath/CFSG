module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A04

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def C24_5P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 Ω K K' W S R R' z u → Nat.card ↥R = 8 →
      ¬ (S : Subgroup G) ≤ MGrp Ω W ∨ TwoSubgroupsFourGenerated G

section SetUp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem not_mem_inf_of_orderOf_four (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hne : K' ≠ K) {u : G} (hu4 : orderOf u = 4) (huK : u ∈ K) (huK' : u ∈ K') : False := by
  have := Sec6Gen.eq_of_le_of_le hΩ hK hK' (IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers, hu4]; norm_num)) (by rw [Nat.card_zpowers, hu4])
    (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr huK')
  exact hne this.symm

theorem c24_setup (hs : Hyp23 Ω K K' z) {W : Subgroup G} (hW : W ∈ WSet Ω) (hzW : z ∈ W)
    (hS4 : MuIsoS4 Ω W) (hZ : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    ∃ (S : Sylow 2 G) (R R' : Subgroup G) (b b' : G), b ∈ K ⊓ W ∧ b' ∈ K' ⊓ W ∧
      orderOf b = 4 ∧ orderOf b' = 4 ∧ Hyp24 Ω K K' W S R R' z (b * b') := by
  have hst : AscStand Ω K := hs.1.stand
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.1.hK'.1
  have hKK' : K' ≠ K := hs.1.hne
  have hz : IsUniqueInvolution K z := hs.1.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.1.hK'
  have hW2 : IsPGroup 2 W := Sec7.isPGroup_of_mem_WSet hW
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw z hzW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ K) K :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hst.cls.isSubnormal_of_uniqueInvolution hK hz)
  have hR' : IsSylow2In (T ⊓ K') K' :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hst.cls.isSubnormal_of_uniqueInvolution hK' hz')
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hWS : W ≤ (S : Subgroup G) := hWT.trans hTS
  have hRS : T ⊓ K ≤ (S : Subgroup G) := inf_le_left.trans hTS
  have hR'S : T ⊓ K' ≤ (S : Subgroup G) := inf_le_left.trans hTS
  obtain ⟨x₁, hx₁, o₁⟩ :=
    T7C.exists_orderOf_four_mem_inf hΩ hW hWS hK hR hRS hz
  obtain ⟨x₂, hx₂, o₂⟩ :=
    T7C.exists_orderOf_four_mem_inf hΩ hW hWS hK' hR' hR'S hz'
  have s₁ : x₁ * x₁ = z := Q3.PhilipHall.Frame.TwinPerp.sq_eq_of_orderOf_four hz hx₁.1 o₁
  have s₂ : x₂ * x₂ = z := Q3.PhilipHall.Frame.TwinPerp.sq_eq_of_orderOf_four hz' hx₂.1 o₂
  have hc : x₁ * x₂ = x₂ * x₁ := hWab x₁ hx₁.2 x₂ hx₂.2
  have hx₁₂ : x₁ ∈ K ⊓ W := ⟨hx₁.1, hx₁.2⟩
  have hx₂₂ : x₂ ∈ K' ⊓ W := ⟨hx₂.1, hx₂.2⟩
  refine ⟨S, T ⊓ K, T ⊓ K', x₁, x₂, hx₁₂, hx₂₂, o₁, o₂, hs, hW, hzW, hS4, hZ, hWS,
    ⟨mem_RSet_of_isSylow2In hK hR, inf_le_right, hRS⟩,
    ⟨mem_RSet_of_isSylow2In hK' hR', inf_le_right, hR'S⟩,
    Subgroup.mul_mem_sup hx₁.1 hx₂.1, W.mul_mem hx₁.2 hx₂.2, ?_, ?_, ?_⟩
  · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
      _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hc]
      _ = (x₁ * x₁) * (x₂ * x₂) := by group
      _ = 1 := by rw [s₁, s₂, hz.sq]
  · intro he
    refine not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem hx₁.1
  · intro he
    refine not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ hx₂.1
    have : x₂ = x₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hx₁.1) hz.mem

theorem c24_5_proved : C24_5P := by
  intro G _ _ _ Ω K K' W S R R' z u hyp h8
  by_cases hSM : (S : Subgroup G) ≤ MGrp Ω W
  · exact Or.inr (T7C2.twoSubgroupsFourGenerated_of_le_MGrp hyp.std.setting hyp.data h8 hSM)
  · exact Or.inl hSM

end SetUp

end Asc77

end CFSG.ClassicalInvolution.Q8P
