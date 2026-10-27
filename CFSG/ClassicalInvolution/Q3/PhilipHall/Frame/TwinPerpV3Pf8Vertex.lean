module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Hyp51

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Vertex





section Datum

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem inv_first_eq (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁⁻¹ = u₁ * z := by
  have h1 : u₁ * u₁ = z := h.sq₁
  have hz : z * z = 1 := h.hz.sq
  rw [inv_eq_iff_mul_eq_one]
  calc u₁ * (u₁ * z) = (u₁ * u₁) * z := by group
    _ = z * z := by rw [h1]
    _ = 1 := hz

theorem inv_first_mul (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁⁻¹ * u₂ = u₁ * u₂ * z := by
  rw [inv_first_eq h]
  calc u₁ * z * u₂ = u₁ * (z * u₂) := by group
    _ = u₁ * (u₂ * z) := by rw [h.comm_z₂]
    _ = u₁ * u₂ * z := by group

theorem closure_inv_first (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁⁻¹ * u₂, z, u₂ * u₃} : Set G) =
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [inv_first_mul h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hzB
    · exact hzB
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · have e : u₁ * u₂ = (u₁⁻¹ * u₂) * z := by
        rw [inv_first_mul h, mul_assoc, h.hz.sq, mul_one]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

theorem _root_.CFSG.ClassicalInvolution.A7T22.Hyp22G.inv_first
    (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : A7T22.Hyp22G Ω K K' K₃ z u₁⁻¹ u₂ u₃ where
  hyp := h.hyp
  mem := h.mem
  hz := h.hz
  subn := h.subn
  hK' := h.hK'
  hne := h.hne
  hK₃ := h.hK₃
  hK₃K := h.hK₃K
  hK₃K' := h.hK₃K'
  hu₁ := ⟨K.inv_mem h.hu₁.1, by rw [orderOf_inv]; exact h.hu₁.2⟩
  hu₂ := h.hu₂
  hu₃ := h.hu₃
  hB := by rw [closure_inv_first h]; exact h.hB

end Datum

section Named

variable {n : ℕ}

@[expose] def V3Hyp51U1 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂)

theorem v3Hyp51U_of_vertex (h : V3Hyp51U1 n) : V3Hyp51U n := by
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d
  refine ⟨h Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d, ?_⟩
  have h2 := h Y R S t hP h3 hE K K' K₃ u₁⁻¹ u₂ u₃ d.inv_first
  rw [closure_inv_first d, inv_first_mul d] at h2
  exact h2

end Named

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
