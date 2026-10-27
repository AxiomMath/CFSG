module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238NQ

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem insp1238NonQ_of_F4
    (h3214 : Stmt3_2_14_F4) : Insp1238NonQ_F4 := by
  intro G _ _ T L V hyp ψ e _ hKe K₀ hKeK₀ hK₀ hTK₀ hq hJ hZ
  exact nonQ_core_F4 h3214 hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hK₀ hTK₀ hKe hKeK₀ hq hJ hZ

end CFSG.Quasithin.H13.A7
