module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBUni

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

theorem kd292CaseBSylow_holds : KD292CaseBSylow := by
  intro p Y _ _ P x z L hcfg hshape T hT2 hxN _ hTL
  have hmodel : LinUniModelLin p x L ∨ LinUniModelUni p x L := hshape.model
  rcases hmodel with hlin | huni
  · exact I292CaseB.kd292CaseBSylow_lin p Y P x z L hcfg hshape.zero hlin T hT2 hxN hTL
  · exact I292CaseB.kd292CaseBSylow_uni p Y P x z L hcfg hshape.zero huni T hT2 hxN hTL

theorem kd292CaseBConstr_holds : KD292CaseBConstr := by
  intro p Y _ _ P x z L hcfg hshape T hT2 hxN _ hTL
  have hmodel : LinUniModelLin p x L ∨ LinUniModelUni p x L := hshape.model
  rcases hmodel with hlin | huni
  · exact I292CaseB.kd292CaseBConstr_lin p Y P x z L hcfg hshape.zero hlin T hT2 hxN hTL
  · exact I292CaseB.kd292CaseBConstr_uni p Y P x z L hcfg hshape.zero huni T hT2 hxN hTL

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
