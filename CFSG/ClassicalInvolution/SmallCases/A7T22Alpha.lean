module

public import CFSG.ClassicalInvolution.SmallCases.A7T22Hyp

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

@[expose] def AlphaConst (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∀ (K K' K₃ : Subgroup G) (u₁ u₂ u₃ : G), Hyp22G Ω K K' K₃ z u₁ u₂ u₃ →
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) →
        IsElemAbelian2 A 2 → alphaOf A = alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G))

namespace Hyp22G

omit [Finite G] in
theorem comm_gen (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
  have hc12 : Commute u₁ u₂ := h.comm₁₂
  have hc13 : Commute u₁ u₃ := h.comm₁₃
  have hc23 : Commute u₂ u₃ := h.comm₂₃
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)
  have hmix : Commute (u₁ * u₂) (u₂ * u₃) :=
    Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hcu₁₂.eq
  · exact hmix.eq
  · exact hcu₁₂.symm.eq
  · rfl
  · exact hcu₂₃.symm.eq
  · exact hmix.symm.eq
  · exact hcu₂₃.eq
  · rfl

omit [Finite G] in
theorem isElemAbelian_B (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian 2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  have hcomm := T7A.commutes_closure h.comm_gen
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact h.hB.2 x hx

omit [Finite G] in
theorem B_le_centralizer (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq

omit [Finite G] in
theorem closure_12_le (_h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_fst
  · exact T7B.mem_closure_snd

omit [Finite G] in
theorem closure_23_le (_h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_thd
  · exact T7B.mem_closure_snd

omit [Finite G] in
theorem closure_13_le (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h.mem_B_13
  · exact T7B.mem_closure_snd

theorem isElemAbelian2_closure_23 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₂ * u₃, z} : Set G)) 2 :=
  h.rotate.isElemAbelian2_closure

theorem isElemAbelian2_closure_13 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₃, z} : Set G)) 2 := by
  have h' := h.rotate.rotate.isElemAbelian2_closure
  rwa [← h.comm₁₃] at h'

omit [Finite G] in
theorem natCard_B (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Nat.card ↥(Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) = 8 := by
  have := h.hB.1
  norm_num at this
  exact this

theorem alpha_23 (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (hα K K' K₃ u₁ u₂ u₃ h).2 _ h.closure_23_le h.isElemAbelian2_closure_23

theorem alpha_13 (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (hα K K' K₃ u₁ u₂ u₃ h).2 _ h.closure_13_le h.isElemAbelian2_closure_13

end Hyp22G

theorem alphaConst_of_hyp51
    (h51 : ∀ (K K' K₃ : Subgroup G) (u₁ u₂ u₃ : G), Hyp22G Ω K K' K₃ z u₁ u₂ u₃ →
      Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G))) :
    AlphaConst Ω z := fun K K' K₃ u₁ u₂ u₃ h =>
  lemma54_odd_and_eq (h51 K K' K₃ u₁ u₂ u₃ h) h.closure_12_le h.isElemAbelian2_closure

namespace Hyp22G

theorem oddCore_le_normalizer_alpha (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha h.isElemAbelian_B h.natCard_B h.B_le_centralizer
    (hα K K' K₃ u₁ u₂ u₃ h).2

theorem third_le_normalizer_alpha (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ := h.hyp
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := h.subn K₃ h.hK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := Sec6Gen.comm_le_oddCore_of_twin hΩ h.mem hK₃Ω h.hK₃K.symm h.hz h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₁.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hc₂ : ⁅u₂, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := Sec6Gen.comm_le_oddCore_of_twin hΩ h.hK'.1 hK₃Ω h.hK₃K'.symm h.hzK' h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₂.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hu₁C
  have hcomm : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have e : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ = (u₁ * ⁅u₂, ℓ⁆ * u₁⁻¹) * ⁅u₁, ℓ⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN _).mp hc₂) hc₁
  exact T7B.mem_normalizer_alphaOf_of_commutator h.sq_12 hzt hℓC hcomm
    (h.oddCore_le_normalizer_alpha hα)

theorem le_normalizer_alpha (hα : AlphaConst Ω z) (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, h.third_le_normalizer_alpha hα⟩
  · have := h.rotate.third_le_normalizer_alpha hα
    rwa [h.alpha_23 hα] at this
  · have := h.rotate.rotate.third_le_normalizer_alpha hα
    rwa [← h.comm₁₃, h.alpha_13 hα] at this

end Hyp22G

end CFSG.ClassicalInvolution.A7T22
