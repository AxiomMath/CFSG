module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YDCat
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.D4XN
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Solomon.Coordinator

section Certified

set_option linter.unusedSectionVars false


theorem d4BigNormalizes_holds
    (G : Type) [Group G] [Finite G] : D4BigNormalizes G := by
  intro X B L hX hB hBX hr hL hD4 hnD4
  by_contra hnL
  have hw : catalogIs (PSimple 3 L) weakExcIndex :=
    weakExc_of_not_normalizes tables112_holds tableL2_unconditional tables112Types_holds
      tables112More_holds hX hB hBX hr hL hnL
  have hM22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 := by
    have h := sporadicOrdersTable_holds TauCeti.SporadicName.M22
    have e22 : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd TauCeti.SporadicName.M22 = 443520 :=
      rfl
    rw [h, e22]
  exact not_weakExc_of_isD4big lieOrderBridge_holds hM22 hD4 hnD4 hw

end Certified

end CFSG.LocalAnalysis.GLTheoremA.D4Y
