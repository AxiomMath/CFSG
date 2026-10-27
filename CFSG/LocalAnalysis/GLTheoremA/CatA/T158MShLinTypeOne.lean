module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOneW
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundNonCommLinW

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem t158LinTypeOneW_of (hLB : T171Sh.LinBlockInnDiag) : T158LinTypeOneW := by
  intro G _ _ p N n L J A d b K _ _ hcard hN θ hact hS hw hJ hnonID M hc
  by_cases hcomm : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ =
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩
  · exact linTypeOne_commuting_of_wSetup hLB hcard θ hact hS hw hnonID M hc hcomm
  · exact linTypeOneNonComm_of_wSetup hcard hN θ hact hS hw hJ M hc hcomm

end CFSG.LocalAnalysis.GLTheoremA.T158

end
