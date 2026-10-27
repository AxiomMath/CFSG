module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CICells
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CIU38
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CITD4Cell

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

structure T263OpenCellsRest : Prop where
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


theorem t263OpenCells_of_rest (h : T263OpenCellsRest) : T263OpenCells :=
  ⟨t263CaseIx_lin, t263CaseIx_uni, t263CaseIx_symp, t263CaseIx_orth, t263CaseIx_twOrth, t263CaseIx_e6,
    t263CaseIx_exc, t263CaseIx_td4, t263CaseIx_ree, t263CaseIx_u38, t263CaseIxTD4_holds, h.desc_lin, h.desc_uni,
    h.desc_symp, h.desc_orth, h.desc_twOrth, h.desc_e6, h.desc_exc, h.desc_td4, h.desc_ree, h.desc_u38⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
