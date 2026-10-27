module

public import CFSG.GF2Type.Smith1979W3.NoNondeg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.LargeExtraspecial

theorem dw3NoTS2_of_noNondeg
    (h1 : DW3NoNondeg) :
    DW3NoTS2 := by
  intro G _ _ _ S hw hnwc W hW hdim hq
  have hP : DW.NondegWeaklyClosed S := by
    intro U hU hnd h0 htop g hgQ
    exfalso
    refine (h1 G S hw hnwc U hU h0 htop) ?_
    show IsCompl U (LinearMap.BilinForm.orthogonal S.q.polarBilin U)
    rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint S.polarBilin_isRefl, disjoint_iff]
    exact hnd
  obtain ⟨g₀, hg₀Q, hg₀⟩ := hnwc
  have h2 : 2 ≤ S.width := by omega
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  have hfin := DW.finrank_eq_widthN_of_nondeg (S := S) (g₀ := g₀) (W := W)
    CFSG.Timmesfeld.arsInput
    (DW.dw2OutInspectionInputN_of_cert DW.dw2FieldInput
      CFSG.LargeExtraspecial.s12ExcModuleInputN) h2 hP hg₀Q hg₀ hW hq hW0
  omega

theorem dwSplitWidthThree_of_noNondeg
    (h1 : DW3NoNondeg) (h6 : DW3CaseIINonsplit) : DWSplitWidthThree :=
  dwSplitWidthThree_of h1 (dw3NoTS2_of_noNondeg h1) h6

theorem dwSplitWidthThree_of_caseIINonsplit
    (h6 : DW3CaseIINonsplit) : DWSplitWidthThree :=
  dwSplitWidthThree_of_noNondeg dw3NoNondeg h6

end CFSG.GF2Type.Smith1979W3
