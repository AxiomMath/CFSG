module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameVertex
public import CFSG.ClassicalInvolution.SmallCases.A7T22H51

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

section VertexZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem hyp51At_z_of_hyp22G (hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M)
    (h : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) z := by
  have hΩ := h.hyp
  have hB := h.isElemAbelian_B
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) :=
    Subgroup.subset_closure (by simp)
  have huB : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hz1 : z ≠ 1 := h.hz.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique h.hz
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique h.hzK'
  have hKsub := isSubnormal_of_hypOmegaGen hΩ h.mem h.hz
  have hK'sub := isSubnormal_of_hypOmegaGen hΩ h.hK'.1 h.hzK'
  have hx' : u₁ ∈ Subgroup.centralizer ({z} : Set G) := hKz h.hu₁.1
  have hy' : u₂ ∈ Subgroup.centralizer ({z} : Set G) := hK'z h.hu₂.1
  have huC : u₁ * u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ hx' hy'
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll
      (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) z L → False := by
    intro L hL hmov
    have hxm : oddQuotMk z ⟨u₁ * u₂, huC⟩ ∈
        modOdd z (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) :=
      oddQuotMk_mem_modOdd huB huC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 huB h.mul_ne_one h.mul_ne_z huC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    apply hwne
    have hcx : ∀ v ∈ L, v * oddQuotMk z ⟨u₁, hx'⟩ = oddQuotMk z ⟨u₁, hx'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨u₁, hx'⟩⁆ ∈ ⁅L, modOdd z K⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd h.hu₁.1 hx')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hKsub (hsolv K h.mem) hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcy : ∀ v ∈ L, v * oddQuotMk z ⟨u₂, hy'⟩ = oddQuotMk z ⟨u₂, hy'⟩ * v := by
      intro v hv
      have h1 : ⁅v, oddQuotMk z ⟨u₂, hy'⟩⁆ ∈ ⁅L, modOdd z K'⁆ :=
        Subgroup.commutator_mem_commutator hv (oddQuotMk_mem_modOdd h.hu₂.1 hy')
      rw [TwinFrame.commutator_component_modOdd_of_solvable hK'sub (hsolv K' h.hK'.1) hL,
        Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have e1 : oddQuotMk z ⟨u₁ * u₂, huC⟩ = oddQuotMk z ⟨u₁, hx'⟩ * oddQuotMk z ⟨u₂, hy'⟩ := by
      rw [← map_mul]
      rfl
    rw [e1, mul_assoc, ← hcy w hw, ← mul_assoc, ← hcx w hw, mul_assoc]
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end VertexZ

section Vertices


@[expose] def V3Hyp51U (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂) ∧
            Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂ * t)

theorem v3Hyp51B_of_vertices {n : ℕ} (hU : V3Hyp51U n) : V3Hyp51B n := by
  intro Y _ _ R S t h h3 hE K K' K₃ u₁ u₂ u₃ d
  have hC := CoreData.of_S h.core
  have hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M := by
    rintro _ ⟨g, rfl⟩
    have hR := Q8Datum.isSolvable hC.datum
    have hK : Group.IsSolvable ↥(tightCore R) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
        (Subgroup.inclusion_injective _)
    exact isSolvable_conjSub_of hK g
  have d1 := d.rotate
  have d2 := d1.rotate
  have hB1 : Subgroup.closure ({u₂ * u₃, t, u₃ * u₁} : Set Y) =
      Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) := d.closure_rotate
  have hB2 : Subgroup.closure ({u₃ * u₁, t, u₁ * u₂} : Set Y) =
      Subgroup.closure ({u₂ * u₃, t, u₃ * u₁} : Set Y) := d1.closure_rotate
  have V0 := hU Y R S t h h3 hE K K' K₃ u₁ u₂ u₃ d
  have V1 := hU Y R S t h h3 hE K' K₃ K u₂ u₃ u₁ d1
  have V2 := hU Y R S t h h3 hE K₃ K K' u₃ u₁ u₂ d2
  rw [hB1] at V1
  rw [hB2, hB1] at V2
  refine ⟨d.isElemAbelian_B, d.natCard_B, fun c hc hc1 => ?_⟩
  rcases d.mem_B_cases hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · rw [e]; exact V0.1
  · rw [e]; exact hyp51At_z_of_hyp22G hsolv d
  · rw [e]; exact V1.1
  · rw [e]; exact V0.2
  · have e' : c = u₃ * u₁ * t := by
      rw [e]
      calc u₁ * u₂ * (u₂ * u₃) = u₁ * (u₂ * u₂) * u₃ := by group
        _ = u₁ * t * u₃ := by rw [d.sq₂]
        _ = t * u₁ * u₃ := by rw [← d.comm_z₁]
        _ = t * (u₃ * u₁) := by rw [mul_assoc, d.comm₁₃]
        _ = (t * u₃) * u₁ := by rw [← mul_assoc]
        _ = (u₃ * t) * u₁ := by rw [d.comm_z₃]
        _ = u₃ * (t * u₁) := by rw [mul_assoc]
        _ = u₃ * (u₁ * t) := by rw [d.comm_z₁]
        _ = u₃ * u₁ * t := by rw [← mul_assoc]
    rw [e']; exact V2.2
  · have e' : c = u₂ * u₃ * t := by
      rw [e]
      calc t * (u₂ * u₃) = (t * u₂) * u₃ := by rw [← mul_assoc]
        _ = (u₂ * t) * u₃ := by rw [d.comm_z₂]
        _ = u₂ * (t * u₃) := by rw [mul_assoc]
        _ = u₂ * (u₃ * t) := by rw [d.comm_z₃]
        _ = u₂ * u₃ * t := by rw [← mul_assoc]
    rw [e']; exact V1.2
  · have e' : c = u₃ * u₁ := by
      rw [e]
      calc u₁ * u₂ * t * (u₂ * u₃) = u₁ * u₂ * (t * u₂) * u₃ := by group
        _ = u₁ * u₂ * (u₂ * t) * u₃ := by rw [d.comm_z₂]
        _ = u₁ * (u₂ * u₂) * (t * u₃) := by group
        _ = u₁ * t * (t * u₃) := by rw [d.sq₂]
        _ = u₁ * (t * t) * u₃ := by group
        _ = u₁ * u₃ := by rw [d.hz.sq]; group
        _ = u₃ * u₁ := d.comm₁₃
    rw [e']; exact V2.1

end Vertices

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
