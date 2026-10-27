module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsCo2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

section G2Certs


theorem cfgIRankS_of_residual
    {p : ℕ}
    (hres : ∀ row : S8.Row, row ≠ S8.Row.th → row ≠ S8.Row.co2 → p = row.prime →
      CfgIRankRow p row) :
    CfgIRankS p := by
  intro row hpr
  by_cases h1 : row = S8.Row.th
  · subst h1
    have hp3 : p = 3 := hpr
    subst hp3
    exact cfgIRank_th_three
  by_cases h2 : row = S8.Row.co2
  · subst h2
    have hp3 : p = 3 := hpr
    subst hp3
    exact cfgIRank_co2_three
  exact hres row h1 h2 hpr

end G2Certs

section UnionCerts


theorem cfgIAt_of_residual
    {G : Type} [Group G] [Finite G] {p : ℕ}
    (hres : ∀ row : S8.Row, row ≠ S8.Row.th → row ≠ S8.Row.co2 → p = row.prime →
      CfgIRankRow p row) :
    S8.L89.CfgIAt G p :=
  cfgIAt_of_S (cfgIRankS_of_residual hres)

end UnionCerts

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
