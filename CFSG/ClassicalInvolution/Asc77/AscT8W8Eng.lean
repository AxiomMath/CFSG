module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8W

variable {G : Type} [Group G] [Finite G]

theorem layerJoin_le_of_closureE {Y H : Subgroup G} (hO : oddCoreOf Y ≤ H)
    (S : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y))
    (hS : S ⊆ (((H.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))
      : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)))
    (hgen : Subgroup.closure S = ⊤) : Y ≤ H := by
  intro w hw
  have hmem : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Y))
      (⟨w, hw⟩ : ↥(Y)) : (↥Y ⧸ classicalInvolutionOddCore ↥Y))
        ∈ ((H.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))) := by
    have h1 : Subgroup.closure S
      ≤ ((H.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))
        := (Subgroup.closure_le _).mpr hS
    rw [hgen] at h1
    exact h1 (Subgroup.mem_top _)
  obtain ⟨h, hh, hhw⟩ := hmem
  have h2 : h⁻¹ * ⟨w, hw⟩ ∈ classicalInvolutionOddCore ↥(Y) :=
    QuotientGroup.eq.mp hhw
  have h3 : (h : G)⁻¹ * w ∈ oddCoreOf (Y) :=
    mem_oddCoreOf_iff.mpr ⟨(Y).mul_mem ((Y).inv_mem h.2) hw,
      by convert h2 using 1⟩
  have hhH : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
  have : w = (h : G) * ((h : G)⁻¹ * w) := by group
  rw [this]
  exact H.mul_mem hhH (hO h3)

theorem mem_layerImage_of_fixedE {Y H : Subgroup G} {y : G}
    (hCy : Subgroup.centralizer ({y} : Set G) ≤ H) (u : (↥Y ⧸ classicalInvolutionOddCore ↥Y))
    (hlift : ∃ w : ↥Y, y * (w : G) * y⁻¹ = w ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) w
        : (↥Y ⧸ classicalInvolutionOddCore ↥Y)) = u) :
    u ∈ ((H.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))) := by
  obtain ⟨w, hw, rfl⟩ := hlift
  refine ⟨w, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  apply hCy
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (w : G) * y = (y * (w : G) * y⁻¹) * y := by rw [hw]
    _ = y * (w : G) := by group

end T8W

end CFSG.ClassicalInvolution.Asc77
