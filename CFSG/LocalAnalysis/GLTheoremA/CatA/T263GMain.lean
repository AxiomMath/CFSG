module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSzCase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

structure T263OpenCells : Prop where
  caseI_lin : T263CaseIx t263GLin
  caseI_uni : T263CaseIx t263GUni
  caseI_symp : T263CaseIx t263GSymp
  caseI_orth : T263CaseIx t263GOrth
  caseI_twOrth : T263CaseIx t263GTwOrth
  caseI_e6 : T263CaseIx t263GE6
  caseI_exc : T263CaseIx t263GExc
  caseI_td4 : T263CaseIx t263GTD4
  caseI_ree : T263CaseIx t263GRee
  caseI_u38 : T263CaseIx t263GU38
  caseI_td4Graph : T263CaseIxTD4
  desc_lin : T263Desc t263GLin
  desc_uni : T263Desc t263GUni
  desc_symp : T263Desc t263GSymp
  desc_orth : T263Desc t263GOrth
  desc_twOrth : T263Desc t263GTwOrth
  desc_e6 : T263Desc t263GE6
  desc_exc : T263Desc t263GExc
  desc_td4 : T263Desc t263GTD4
  desc_ree : T263Desc t263GRee
  desc_u38 : T263Desc t263GU38

section Certs


theorem t263FactGenK_of_openCells
    (h : T263OpenCells) : T263FactGenK :=
  t263FactGenK_of_residuals
    ⟨h.caseI_lin, h.caseI_uni, h.caseI_symp, h.caseI_orth, h.caseI_twOrth, h.caseI_e6, h.caseI_exc, h.caseI_td4,
      t263CaseIx_sz, h.caseI_ree, t263CaseIx_of_vac t263Vac_tits, t263CaseIx_of_vac t263Vac_ambAlt,
      t263CaseIx_of_vac t263Vac_ambU33, t263CaseIx_of_vac t263Vac_l28, h.caseI_u38,
      t263CaseIx_of_vac t263Vac_sz32⟩ h.caseI_td4Graph
    ⟨h.desc_lin, h.desc_uni, h.desc_symp, h.desc_orth, h.desc_twOrth, h.desc_e6, h.desc_exc, h.desc_td4,
      t263Desc_sz, h.desc_ree, t263Desc_of_vac t263Vac_tits, t263Desc_of_vac t263Vac_ambAlt,
      t263Desc_of_vac t263Vac_ambU33, t263Desc_of_vac t263Vac_l28, h.desc_u38, t263Desc_of_vac t263Vac_sz32⟩

theorem t263FactGen_of_openCells
    (h : T263OpenCells) : T263FactGen :=
  t263FactGen_of_K (t263FactGenK_of_openCells h)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
