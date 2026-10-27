module

public import CFSG.GF2Type.Smith1979.CaseIIAssemblyCard
public import CFSG.GF2Type.Smith1979.CaseIIAssemblyExcl
public import CFSG.GF2Type.Smith1979.CaseIIDTwo
public import CFSG.GF2Type.Smith1979.CaseIIFilterMain
public import CFSG.GF2Type.Smith1979.CaseIIFinal
public import CFSG.GF2Type.Smith1979.CaseIIJ4Core
public import CFSG.GF2Type.Smith1979.SixCases
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GF2Type.Smith1980Orth CFSG.ComponentClassification
open CFSG.Assembly (InCatalog KProper)

theorem caseIIStmt_of_inputs (hU : Case2.U43Frob56Free) (hR : Case2.RderFacts) : CaseIIStmt := by
  intro I G _ _ _ hK S hw hirr hnoAll g H C _ t ht ht1 hL h3
  have hNo : NoA2 S g := S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have D : Case2.Data S g t := ⟨H, hNo, C, ht, ht1, hL, h3, hw⟩
  refine ⟨isTypeJ4Core_of_width_six S hw H C, ?_⟩
  obtain ⟨hodd, hq, -⟩ := S5.timmesfeld_5_5 I.hCE (S14.irr_of_not_isReducible hirr) H hNo C
    (S45Q.hyp45Q H C) (by omega)
  have hM : S.M ≠ ⊤ := Case25.M_ne_top_of_isSimpleGroup S
  haveI : IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := hq.2
  have hS := CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hcrit := Case2.critII_X D I.hCE hS hK hM hq hodd
  have hfilter := Case2.filterIIInCatalog_of_bridge
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge (Case25.inCatalog_layer_quotient hK hM hq)
    (Helpers.quasisimple_central_quotient_nonabelian _ hq) D.card_layer_quotient_dvd_orthPlus12
    hcrit.2 (Case2.not_two_pow_eleven_dvd_card_X D I.hCE)
  have hM22 := D.isSporadic_M22_of_filter I.hCE hS hK hM hq hodd hU hR hfilter
  exact isAutTripleM22_of_M22 S hw hirr hodd hq hM22 ⟨_, D.tM_not_mem_layer⟩

end CFSG.GF2Type.Smith1979
