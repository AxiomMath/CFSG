module

public import CFSG.GF2Type.Smith1979.W4C2Main
public import CFSG.GF2Type.Smith1980Orth.Setup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem nonempty_Mbar_equiv_omegaPlus_of_omegaPlusEight {S : Setting G}
    (h : S.S12OmegaPlusEight) : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 4) := by
  obtain ⟨hw, ⟨W, hW, hWs⟩, hΩ⟩ := h
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hΩ' : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate := by
    rw [hΩ, s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
  obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus S.q_nondegenerate (m := 4)
    (by rw [S.finrank_Qt_eq_two_mul_width, hw]) (by norm_num) ⟨W, hW, hWs⟩
  exact ⟨((Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hΩ')).trans e⟩

theorem pattersonCo1Hyp_of_omegaPlusEight [IsSimpleGroup G] {S : Setting G}
    (hnc : ∃ a b : G, a * b ≠ b * a) (h : S.S12OmegaPlusEight) :
    PattersonCo1Hyp G S.z where
  simple := inferInstance
  noncomm := hnc
  orderOf_eq := S.orderOf_z
  extraspecial := Bridge.timmesfeldIsExtraspecial_fstar S
  card := (Bridge.card_fstar S).trans (by rw [h.1])
  quotient := by
    obtain ⟨e⟩ := nonempty_Mbar_equiv_omegaPlus_of_omegaPlusEight h
    exact Bridge.quotientIso_congr_right (Bridge.quotientIso_Mbar S) e

theorem coOneBranch
    [IsSimpleGroup G] (I : Smith1980Orth.TimInputs) (hInsp : Timmesfeld12_3InspectionInput)
    (hPat : PattersonCo1Input) {S : Setting G} (hnc : ∃ a b : G, a * b ≠ b * a)
    (hw : S.width = 4) (hirr : ¬ S.IsReducible) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hA : S.HasTypeAInL g) :
    NativeSporadic.IsSporadic G .Co1 := by
  obtain ⟨α, hαL, -, hαA⟩ := hA
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  rcases W4C2.timmesfeld_12_16_w4 I.hRI I.hARS I.hTri I.hFischer hInsp I.h36 I.hSL haQ hne hw
      ht hαA with hred | h8
  · exact (hirr hred).elim
  · exact hPat G S.z (pattersonCo1Hyp_of_omegaPlusEight hnc h8)

end CFSG.GF2Type.Smith1979.W4As
