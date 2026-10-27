module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fg_inFStar_of_layerModel {P : Type} [Group P] [Finite P] {H : Subgroup P}
    {t : CFSG.Open.StatedLieTag} {n k : ℕ}
    (hsh : ∀ (E : Type) [Group E], LieModel E t n 3 k →
      IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E)
    (hLM : LayerModel ↥H t n k) {J : Subgroup P} (hJ : IsComponentIn J H) : InFStar J := by
  obtain ⟨E, hEn, hLie, h2⟩ := hLM
  obtain ⟨hs, hnc, hF⟩ := hsh ↥E hLie
  haveI := hEn
  let E' : Subgroup P := E.map H.subtype
  have hE'H : E' ≤ H := Subgroup.map_subtype_le E
  have hsub : E'.subgroupOf H = E := Subgroup.comap_map_eq_self_of_injective H.subtype_injective E
  have hEq : ↥E ≃* ↥E' := Subgroup.equivMapOfInjective E H.subtype H.subtype_injective
  have hqE : CFSG.IsQuasisimple ↥E := ff_isQuasisimple_of_simple hs hnc
  have hqE' : CFSG.IsQuasisimple ↥E' := CFSG.LocalCores.isQuasisimple_of_mulEquiv hEq hqE
  have hnE' : (E'.subgroupOf H).Normal := by
    rw [hsub]
    exact hEn
  have hcE' : IsComponentIn E' H := isComponentIn_of_normal hE'H hqE' hnE'
  have hJE : J ≤ E' := by
    have hperf : Group.IsPerfect ↥(J.subgroupOf H) := hJ.2.1.1
    have hle : J.subgroupOf H ≤ E := ff_perfect_le_of_quot_two E h2 (J.subgroupOf H) hperf
    intro j hj
    have hjH : j ∈ H := hJ.1 hj
    have hmem : (⟨j, hjH⟩ : ↥H) ∈ J.subgroupOf H := hj
    exact ⟨⟨j, hjH⟩, hle hmem, rfl⟩
  have hJeq : J = E' := IsComponentIn.eq_of_le hJ hcE' hJE
  rw [InFStar, hJeq]
  exact isFStarGroup_of_mulEquiv hEq hF

theorem fg_shape_psl2 (E : Type) [Group E] (h : LieModel E .PSL 2 3 2) :
    IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E := by
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl2 h
  obtain ⟨hfin, -⟩ := ff_fin_simple_psl2 h
  haveI := hfin
  have hq := ff_isQuasisimple_of_simple hs hnc
  have hquot := ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psl2 h]; norm_num)
  exact ⟨hs, hnc, Or.inr ⟨hq, Or.inl hquot⟩⟩

theorem fg_shape_psp (E : Type) [Group E] (h : LieModel E .PSp 2 3 1) :
    IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E := by
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psp h
  obtain ⟨hfin, -⟩ := ff_fin_simple_psp h
  haveI := hfin
  have hq := ff_isQuasisimple_of_simple hs hnc
  have hquot := ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psp h]; norm_num)
  exact ⟨hs, hnc, Or.inl ⟨hq, Or.inl (Or.inl hquot)⟩⟩

theorem fg_shape_psl3 (E : Type) [Group E] (h : LieModel E .PSL 3 3 1) :
    IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E := by
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psl3 h
  obtain ⟨hfin, -⟩ := ff_fin_simple_psl3 h
  haveI := hfin
  have hq := ff_isQuasisimple_of_simple hs hnc
  have hquot := ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psl3 h]; norm_num)
  exact ⟨hs, hnc, Or.inr ⟨hq, Or.inr (Or.inr (Or.inl hquot))⟩⟩

theorem fg_shape_psu3 (E : Type) [Group E] (h : LieModel E .PSU 3 3 1) :
    IsSimpleGroup E ∧ (∃ a b : E, a * b ≠ b * a) ∧ IsFStarGroup E := by
  obtain ⟨hs, hnc⟩ := ff_simple_of_lieModel_psu3 h
  obtain ⟨hfin, -⟩ := ff_fin_simple_psu3 h
  haveI := hfin
  have hq := ff_isQuasisimple_of_simple hs hnc
  have hquot := ff_lieModel_quot_oddCore h hs (by rw [ff_card_model_psu3 h]; norm_num)
  exact ⟨hs, hnc, Or.inr ⟨hq, Or.inr (Or.inr (Or.inr hquot))⟩⟩

end CFSG.OddStandard.SmallF3.Omega
