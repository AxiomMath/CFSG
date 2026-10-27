module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E6FourStab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LieType.Steinberg.CentralExt.AdjointClosed
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open

section Certs

theorem subsystemGroup_le_toralCentralizer_e6FourToralParam :
    subsystemGroup Tag.E6 K setD ≤ toralCentralizer Tag.E6 K e6FourToralParam := by
  rw [← rootSpan_rootCharKernel_e6FourToralParam]
  exact rootSpan_rootCharKernel_le_toralCentralizer e6FourToralParam

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
