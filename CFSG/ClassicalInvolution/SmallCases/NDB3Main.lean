module

public import CFSG.ClassicalInvolution.SmallCases.NDB3Vertex
public import CFSG.ClassicalInvolution.SmallCases.NDB2Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

theorem axisFrameSideCore : AxisFrameSideCore p f := by
  intro G _ _ _ K z hS hpsp K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA
  have hp := hS.odd
  have hq := hS.five
  have hΩ : HypOmegaMod p f (𝒞 K) :=
    Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hS.nonabelian
      hp hq K z hS.member hS.below
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hct : Commute t₁ t₂ := hA.ct₁₂
  have hcomm12 : z₁ * z₂ = z₂ * z₁ := by
    rw [← hA.sq₁, ← hA.sq₂]
    exact ((hct.mul_left hct).mul_right (hct.mul_left hct)).eq
  have h21 : z₂ * z₁ = z₃ := hcomm12.symm.trans hA.prod
  have h31 : z₃ * z₁ = z₂ := by
    rw [← hA.prod, mul_assoc, ← hcomm12, ← mul_assoc, hz₁c.sq, one_mul]
  have hsw := Vertex.axis_swap (z₁ := z₁) (z₂ := z₂) (t₃ := t₃) hA.ct₁₂
  have hro := Vertex.axis_rot hz₁c.sq hA.prod hA.ct₁₃ hA.ct₂₃
  have h₁S : K₁ ∈ ({K₁, K₂, K₃} : Set (Subgroup G)) := Set.mem_insert _ _
  have h₂S : K₂ ∈ ({K₁, K₂, K₃} : Set (Subgroup G)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have h₃S : K₃ ∈ ({K₁, K₂, K₃} : Set (Subgroup G)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have hz₁B : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂B : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hz₃B : z₃ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := hA.prod ▸ Subgroup.mul_mem _ hz₁B hz₂B
  have hinv : ∀ a : G, IsFrameInvolution p f ({K₁, K₂, K₃} : Set (Subgroup G)) a →
      a = z₁ ∨ a = z₂ ∨ a = z₃ := by
    rintro a ⟨M, hM, ha⟩
    have hu := fun {L : Subgroup G} {b : G} (hb : IsClassicalMember p f L b) =>
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hb
    rcases hM with rfl | rfl | rfl
    · exact Or.inl ((hu ha).eq (hu hA.cls₁))
    · exact Or.inr (Or.inl ((hu ha).eq (hu hA.cls₂)))
    · exact Or.inr (Or.inr ((hu ha).eq (hu hA.cls₃)))
  refine ⟨hA.elem, hA.card.ge, ?_, ⟨K₁, h₁S⟩, ?_, fun a _ ha => ?_, fun a _ ha => ?_⟩
  · rintro M (rfl | rfl | rfl)
    exacts [hA.mem₁, hA.mem₂, hA.mem₃]
  · rintro M (rfl | rfl | rfl)
    exacts [⟨z₁, hz₁B, hA.cls₁⟩, ⟨z₂, hz₂B, hA.cls₂⟩, ⟨z₃, hz₃B, hA.cls₃⟩]
  · rcases hinv a ha with rfl | rfl | rfl
    · exact generation_axis_vertex hΩ hp hq hA.mem₁ hA.cls₁ (hpsp K₁ hA.mem₁ _ hA.cls₁)
        ⟨hA.mem₂, hA.tq₂₁⟩ hA.cls₂ ⟨hA.mem₃, hA.tq₃₁⟩ hA.cls₃ hA.prod hA.ht₁ hA.ht₂ hA.ht₃
        hA.sq₁ hA.sq₂ hA.sq₃ hA.ct₁₂ hA.ct₁₃ hA.elem hA.card
    · have h := generation_axis_vertex hΩ hp hq hA.mem₂ hA.cls₂ (hpsp K₂ hA.mem₂ _ hA.cls₂)
        ⟨hA.mem₁, hA.tq₁₂⟩ hA.cls₁ ⟨hA.mem₃, hA.tq₃₂⟩ hA.cls₃ h21 hA.ht₂ hA.ht₁ hA.ht₃
        hA.sq₂ hA.sq₁ hA.sq₃ hA.ct₁₂.symm hA.ct₂₃ (hsw ▸ hA.elem) (hsw ▸ hA.card)
      rwa [hsw] at h
    · have h := generation_axis_vertex hΩ hp hq hA.mem₃ hA.cls₃ (hpsp K₃ hA.mem₃ _ hA.cls₃)
        ⟨hA.mem₁, hA.tq₁₃⟩ hA.cls₁ ⟨hA.mem₂, hA.tq₂₃⟩ hA.cls₂ h31 hA.ht₃ hA.ht₁ hA.ht₂
        hA.sq₃ hA.sq₁ hA.sq₂ hA.ct₁₃.symm hA.ct₂₃.symm (hro ▸ hA.elem) (hro ▸ hA.card)
      rwa [hro] at h
  · rcases hinv a ha with rfl | rfl | rfl
    · exact link_axis_vertex hΩ hp hq hA.mem₁ hA.cls₁ (hpsp K₁ hA.mem₁ _ hA.cls₁)
        ⟨hA.mem₂, hA.tq₂₁⟩ hA.cls₂ hA.cls₃ hA.prod h₁S h₂S
    · have h := link_axis_vertex (t₁ := t₂) (t₂ := t₁) (t₃ := t₃) hΩ hp hq hA.mem₂ hA.cls₂
        (hpsp K₂ hA.mem₂ _ hA.cls₂) ⟨hA.mem₁, hA.tq₁₂⟩ hA.cls₁ hA.cls₃ h21 h₂S h₁S
      rwa [hsw] at h
    · have h := link_axis_vertex (t₁ := t₃) (t₂ := t₁) (t₃ := t₂) hΩ hp hq hA.mem₃ hA.cls₃
        (hpsp K₃ hA.mem₃ _ hA.cls₃) ⟨hA.mem₁, hA.tq₁₃⟩ hA.cls₁ hA.cls₂ h31 h₃S h₁S
      rwa [hro] at h

theorem axisFrameSide : AxisFrameSide p f :=
  AxisFrameSide.of_core p f (axisFrameSideCore p f)

end CFSG.ClassicalInvolution.NDB
