module

public import CFSG.GF2Type.Smith1979W3.NoTS2
public import CFSG.LargeExtraspecial.DW3CaseIIGood
public import CFSG.LargeExtraspecial.DW3CaseIIBad
public import CFSG.LargeExtraspecial.CorBGL32
public import CFSG.LargeExtraspecial.S8CBFMain
public import CFSG.LargeExtraspecial.S8CBF3D4Sect
public import CFSG.Timmesfeld.CorollaryB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.LargeExtraspecial

theorem dw3CaseIINonsplit :
    DW3CaseIINonsplit := by
  intro G _ _ _ S hw hnwc A hEA hA hM _ hII hNS
  haveI := hEA
  obtain ⟨g₀, hg₀Q, hg₀z⟩ := hnwc
  have hg₀A : g₀ * S.z * g₀⁻¹ ∈ A := hII g₀ hg₀Q
  by_cases hgood : ∃ g : G, g * S.z * g⁻¹ ∈ A ∧ g * S.z * g⁻¹ ≠ S.z ∧ A ≤ S.Qa g
  · obtain ⟨g, hgA, hgz, hgQa⟩ := hgood
    have hall := (hA.caseII_hyp_of_good hM hgA hgz hgQa).2
    obtain ⟨e⟩ := hA.nonempty_Mbar_mulEquiv_of_surjective hM
      (hA.resAt_surjective_of_good hM hgA hgz hgQa)
    rw [hw] at e
    exact S8.false_of_forall_conj_mem_QG_of_mulEquiv_GL32 CFSG.Timmesfeld.timmesfeldCorBInput
      (S8.corBListFacts_of S8.corBSectResidual) S
      (fun h hyM => hA.conj_mem_QG_of_mem_M_of_good hM hII hw hall hgA hgz hNS hyM) e
  · push Not at hgood
    exact hA.false_of_bad_of_noInvariantCompl hM hII hw hgood hNS hg₀A hg₀z

theorem dwSplitWidthThree :
    DWSplitWidthThree :=
  dwSplitWidthThree_of_caseIINonsplit dw3CaseIINonsplit

end CFSG.GF2Type.Smith1979W3
