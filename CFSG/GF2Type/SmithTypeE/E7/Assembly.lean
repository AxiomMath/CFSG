module

public import CFSG.GF2Type.SmithTypeE.E7.Defs
public import CFSG.GF2Type.SmithTypeE.E7Outcome
public import CFSG.GF2Type.SmithTypeE.ThreeFour
public import CFSG.Blueprint.SourceClassicalTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open Subgroup Equiv CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.Bridge CFSG.RankThree.PartTwo.Sec21
open scoped MatrixGroups

theorem smithE7ThreeFourInput_of (hAS : AschbacherSmithWideInput)
    (hDW : DW.DW37Statement) (hHolt : HoltUniqueFixedPointSimple) (hLoc : SmithE7LocalInput)
    (hPath : SmithE7PathInput) : SmithE7ThreeFourInput := by
  intro G _ _ _ S hw hO
  have h2 := factorization_card_of_E7 S hw hO
  obtain ⟨d, e, hd, he, h4⟩ := exists_isConj_orderOf_mul_eq_four_of_two_part hAS hDW S
    (by omega) (by rw [h2, hw]; norm_num)
  refine ⟨fun a b ha hb => ?_, ⟨d, e, hd, he, h4⟩⟩
  have hAlt : ∀ m : ℕ, ¬ Nonempty (G ≃* alternatingGroup (Fin m)) := fun m ⟨φ⟩ =>
    false_of_mulEquiv_alternatingGroup S (p := 13) (c := 63) (by norm_num) (by norm_num) h2
      (by decide) (not_thirteen_dvd_card_M_of_E7 S hw hO) φ
  exact threeFour_of_local_path hHolt S hAlt (hLoc G S hw hO) (hPath G S hw hO) hd he h4
    a b ha hb

theorem smithE7Input_of_threeFour (h : SmithE7ThreeFourInput) : SmithE7Input := by
  intro G _ _ _ S hw hO
  obtain ⟨hprod, hnd⟩ := h G S hw hO
  exact e7_of_threeFourPlus S hw hO (threeFourPlusClass_of_products S hprod) hnd

end CFSG.GF2Type.SmithTypeE
