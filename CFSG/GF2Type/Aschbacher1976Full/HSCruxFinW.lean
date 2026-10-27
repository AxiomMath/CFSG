module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFinW4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

theorem cruxFinW_holds : CruxFinWStmt := by
  intro V _ _ _ b halt hnd hdim N hN hiso
  obtain ⟨m, bs, hm, h1, h2, h3⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      b halt hnd
  obtain rfl : m = 2 := by omega
  exact FinW.finW_core bs b h1 h2 h3 halt N hN hiso

end CFSG.GF2Type.Aschbacher1976Full.HS
