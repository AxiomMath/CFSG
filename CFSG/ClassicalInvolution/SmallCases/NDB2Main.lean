module

public import CFSG.ClassicalInvolution.SmallCases.NDB2Vertex
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

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Vertex

variable {G : Type} [Group G]

theorem not_subset_center [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {c : G}
    (hc : c ≠ 1) : ¬ ({c} : Set G) ⊆ Subgroup.center G := by
  intro h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hZ | hZ
  · exact hc (Subgroup.mem_bot.mp (hZ ▸ h rfl))
  · obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem axis_swap {z₁ z₂ t₁ t₂ t₃ : G} (c₁₂ : t₁ * t₂ = t₂ * t₁) :
    TypeCSetup.axis z₂ z₁ t₂ t₁ t₃ = TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := by
  show Subgroup.closure ({z₂, z₁, t₂ * t₁ * t₃} : Set G) =
    Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G)
  rw [← c₁₂, Set.insert_comm]

theorem axis_rot {z₁ z₂ z₃ t₁ t₂ t₃ : G} (hz₁ : z₁ * z₁ = 1) (hprod : z₁ * z₂ = z₃)
    (c₁₃ : t₁ * t₃ = t₃ * t₁) (c₂₃ : t₂ * t₃ = t₃ * t₂) :
    TypeCSetup.axis z₃ z₁ t₃ t₁ t₂ = TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := by
  have hs : t₃ * t₁ * t₂ = t₁ * t₂ * t₃ := by
    rw [← c₁₃, mul_assoc, ← c₂₃, mul_assoc]
  have hz₂ : z₂ = z₁ * z₃ := by rw [← hprod, ← mul_assoc, hz₁, one_mul]
  show Subgroup.closure ({z₃, z₁, t₃ * t₁ * t₂} : Set G) =
    Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G)
  rw [hs]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · rw [← hprod]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [hz₂]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Subgroup.subset_closure
        (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

end Vertex

variable (p f : ℕ) [Fact p.Prime]

theorem axisHyp51ClassicalCore : AxisHyp51ClassicalCore p f := by
  intro G _ _ _ K z hS hpsp K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hc hc1
  have hΩ : HypOmegaMod p f (𝒞 K) :=
    Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hS.nonabelian
      hS.odd hS.five K z hS.member hS.below
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hA.cls₃
  have hct : Commute t₁ t₂ := hA.ct₁₂
  have hcomm12 : z₁ * z₂ = z₂ * z₁ := by
    rw [← hA.sq₁, ← hA.sq₂]
    exact ((hct.mul_left hct).mul_right (hct.mul_left hct)).eq
  rcases TypeCSetup.mem_closure_pair hz₁c.sq hz₂c.sq hcomm12 hc with rfl | rfl | rfl | rfl
  · exact absurd rfl hc1
  · exact hyp51At_axis_vertex hΩ hS.odd hS.five hS.below
      (Vertex.not_subset_center hS.nonabelian hc1) hA.mem₁ hA.cls₁ (hpsp K₁ hA.mem₁ c hA.cls₁)
      ⟨hA.mem₂, hA.tq₂₁⟩ hA.cls₂ ⟨hA.mem₃, hA.tq₃₁⟩ hA.cls₃ hA.prod hA.ht₁ hA.ht₂ hA.ht₃
      hA.sq₁ hA.sq₂ hA.sq₃ hA.ct₁₂ hA.ct₁₃ hA.ct₂₃ hA.elem hA.card
  · have hsw := Vertex.axis_swap (z₁ := z₁) (z₂ := c) (t₃ := t₃) hA.ct₁₂
    have h := hyp51At_axis_vertex hΩ hS.odd hS.five hS.below
      (Vertex.not_subset_center hS.nonabelian hc1) hA.mem₂ hA.cls₂ (hpsp K₂ hA.mem₂ c hA.cls₂)
      ⟨hA.mem₁, hA.tq₁₂⟩ hA.cls₁ ⟨hA.mem₃, hA.tq₃₂⟩ hA.cls₃ (hcomm12.symm.trans hA.prod) hA.ht₂
      hA.ht₁ hA.ht₃ hA.sq₂ hA.sq₁ hA.sq₃ hA.ct₁₂.symm hA.ct₂₃ hA.ct₁₃ (hsw ▸ hA.elem)
      (hsw ▸ hA.card)
    rwa [hsw] at h
  · have hro := Vertex.axis_rot hz₁c.sq hA.prod hA.ct₁₃ hA.ct₂₃
    have hz₃1 : z₃ ≠ 1 := hA.prod ▸ hc1
    have h31 : z₃ * z₁ = z₂ := by
      rw [← hA.prod, mul_assoc, ← hcomm12, ← mul_assoc, hz₁c.sq, one_mul]
    have h := hyp51At_axis_vertex hΩ hS.odd hS.five hS.below
      (Vertex.not_subset_center hS.nonabelian hz₃1) hA.mem₃ hA.cls₃ (hpsp K₃ hA.mem₃ z₃ hA.cls₃)
      ⟨hA.mem₁, hA.tq₁₃⟩ hA.cls₁ ⟨hA.mem₂, hA.tq₂₃⟩ hA.cls₂ h31 hA.ht₃ hA.ht₁ hA.ht₂ hA.sq₃
      hA.sq₁ hA.sq₂ hA.ct₁₃.symm hA.ct₂₃.symm hA.ct₁₂ (hro ▸ hA.elem) (hro ▸ hA.card)
    rw [hro] at h
    rwa [hA.prod]

theorem axisHyp51Classical : AxisHyp51Classical p f :=
  AxisHyp51Classical.of_core p f (axisHyp51ClassicalCore p f)

end CFSG.ClassicalInvolution.NDB
