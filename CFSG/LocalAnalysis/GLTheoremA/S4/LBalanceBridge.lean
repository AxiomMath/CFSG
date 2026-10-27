module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem lBalanceAt_of_catalogueSchreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) {p : ℕ}
    (hp : p.Prime) : LBalanceAt G p := fun _ _ hK hPX hP =>
  CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_inf_centralizer_le hS hK hp hPX hP

end CFSG.LocalAnalysis.GLTheoremA
