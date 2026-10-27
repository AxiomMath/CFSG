module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child4
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelOrder
public import CFSG.Quasithin.Recognition.M12AscMain

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.Sporadic.Schreier.Co3

theorem isConj_co3ZP_ma
    : IsConj co3ZP (co3MtoP Co3Ident.ma) := by
  refine isConj_iff.2 ⟨⟨Co3Ident.sP, Co3Ident.sP_mem_P⟩, Subtype.ext ?_⟩
  rw [co3MtoP_coe, Co3Ident.coe_ma]
  exact Co3Ident.sP_conj_z'

theorem isConj_fendelA_ma :
    IsConj fendelA Co3Ident.ma :=
  ((fendel_co3_fusion _ Co3Ident.involutions.1).1 isConj_co3ZP_ma).resolve_left
    Co3Ident.ma_ne_co3ZM

theorem fusion_iff_classA
    (x : co3M) (hx : orderOf x = 2) :
    IsConj co3ZP (co3MtoP x) ↔ x = co3ZM ∨ x ∈ Co3Ident.classA := by
  rw [fendel_co3_fusion x hx]
  exact or_congr_right ⟨fun h => (isConj_comm.1 isConj_fendelA_ma).trans h,
    fun h => isConj_fendelA_ma.trans h⟩

theorem fendelInputs_of_asc03
    (hM12 : CFSG.GH74.M12.S_Asc03_simple) : FendelInputs := by
  intro G _ _ hG s θ hθ
  obtain ⟨hH2, hH3⟩ := fendel_order θ hG hθ hM12
  exact ⟨fun x hx => (hH2 x hx).trans (fusion_iff_classA x hx), hH3⟩

theorem childSp6Cover_of_asc03
    (hM12 : CFSG.GH74.M12.S_Asc03_simple) : ChildSp6Cover :=
  childSp6Cover_of_inputs (fendelInputs_of_asc03 hM12)

theorem childSp6Cover
    : ChildSp6Cover :=
  childSp6Cover_of_asc03 CFSG.Quasithin.s_Asc03_simple

end CFSG.EvenSmallLie.SympSix
