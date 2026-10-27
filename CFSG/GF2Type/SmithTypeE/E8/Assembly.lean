module

public import CFSG.GF2Type.SmithTypeE.E8.Defs
public import CFSG.GF2Type.SmithTypeE.E7.Defs
public import CFSG.GF2Type.SmithTypeE.E7Outcome
public import CFSG.GF2Type.SmithTypeE.ThreeFour
public import CFSG.GF2Type.Entry
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GF2Type.SmithTypeE.Parts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup Equiv CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.Bridge CFSG.RankThree.PartTwo.Sec21
open scoped MatrixGroups

theorem smithE8ThreeFourInput_of (hAS : AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (hHolt : HoltUniqueFixedPointSimple) (hLoc : SmithE8LocalInput)
    (hPath : SmithE8PathInput) : SmithE8ThreeFourInput := by
  intro G _ _ _ S hw hE
  have h2 := factorization_card_of_E8 S hw hE
  obtain ⟨d, e, hd, he, h4⟩ := exists_isConj_orderOf_mul_eq_four_of_two_part hAS hDW S
    (by omega) (by rw [h2, hw]; norm_num)
  refine ⟨fun a b ha hb => ?_, ⟨d, e, hd, he, h4⟩⟩
  have hAlt : ∀ m : ℕ, ¬ Nonempty (G ≃* alternatingGroup (Fin m)) := fun m ⟨φ⟩ =>
    false_of_mulEquiv_alternatingGroup S (p := 23) (c := 120) (by norm_num) (by norm_num) h2
      (by decide) (not_twentythree_dvd_card_M_of_E8 S hw hE) φ
  exact threeFour_of_local_path hHolt S hAlt (hLoc G S hw hE) (hPath G S hw hE) hd he h4
    a b ha hb

theorem smithE8Input_of_threeFour (h : SmithE8ThreeFourInput) : SmithE8Input := by
  intro G _ _ _ S hw hE
  obtain ⟨hprod, hnd⟩ := h G S hw hE
  exact e8_of_threeFourPlus S hw hE (threeFourPlusClass_of_products S hprod) hnd

theorem partD_of_smithE7Input (hE7 : SmithE7Input) (hE8 : SmithE8Input) : PartD := by
  intro G _ _ _ hnonab z hz hext hcard Mbar _ hMbar hMs ⟨t, ht2, htext, htcard, htquot⟩
  have hfin : Finite Mbar := by
    obtain ⟨φ, hφ, -⟩ := hMbar
    exact Finite.of_surjective φ hφ
  haveI : IsSimpleGroup Mbar := hMs
  have htext' :
      timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact (timmesfeldIsExtraspecial_iff _).mpr htext
  have htcard' : Nat.card (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) =
      2 ^ (1 + 2 * 16) := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact htcard
  have htquot' : timmesfeldQuotientIso
      (timmesfeldFStar (Subgroup.centralizer ({t} : Set Mbar))) (timmesfeldOmegaPlus 6) := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact htquot
  have hwt : (Setting.ofFStar t ht2 htext').width = 16 := width_ofFStar ht2 htext' htcard'
  obtain ⟨et⟩ := nonempty_mulEquiv_Mbar_ofFStar ht2 htext' htquot'
  have hE7' := hE7 Mbar (Setting.ofFStar t ht2 htext') hwt ⟨et⟩
  have hL : LieModel Mbar .E7 0 2 1 := Or.inr (Or.inl ⟨rfl, by decide, hE7'⟩)
  obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
  have hMbar' : timmesfeldQuotientIso
      (timmesfeldFStar ↥(Subgroup.centralizer ({z} : Set G))) Mbar := by
    rw [← generalizedFitting_eq_timmesfeldFStar]
    exact hMbar
  have hw : (Setting.ofFStar z hz hext').width = 28 := width_ofFStar hz hext' hcard'
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_ofFStar hz hext' hMbar'
  have hE := hE8 G (Setting.ofFStar z hz hext') hw (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL)
  exact Or.inr (Or.inl ⟨rfl, by decide, hE⟩)

theorem partD_of_props (hAS : AschbacherSmithWideInput) (hDW : DW.DW37Statement)
    (hHolt : HoltUniqueFixedPointSimple) (hE7 : SmithE7Input) (hLoc : SmithE8LocalInput)
    (hPath : SmithE8PathInput) : PartD :=
  partD_of_smithE7Input hE7
    (smithE8Input_of_threeFour (smithE8ThreeFourInput_of hAS hDW hHolt hLoc hPath))

end CFSG.GF2Type.SmithTypeE
