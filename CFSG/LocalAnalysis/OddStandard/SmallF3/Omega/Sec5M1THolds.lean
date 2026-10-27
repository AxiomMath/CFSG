module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactRhoStar_of (hS : Asc82SchurU43) : Asc82FactRhoStar := by
  intro G _ _ t L z K₁ K₂ hz2 hL hodd _ hK₁ hK₂ _ hcomm hprod q hq hq4 c hc hcK hcz
  exact sec5m1t_main hS hz2 hL hodd hK₁ hK₂ hcomm hprod hq hq4 hc hcK hcz

end CFSG.OddStandard.SmallF3.Omega
