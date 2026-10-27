module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TI117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNRed
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.D4XN
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Solomon.Coordinator

section Certified



theorem isD4two_not_weakExc
    {S : Type} [Group S] [Finite S] (h4 : catalogIs S S9.isD4two) :
    ¬ catalogIs S weakExcIndex := by
  have hM22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 := by
    have h := sporadicOrdersTable_holds TauCeti.SporadicName.M22
    have e22 : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd TauCeti.SporadicName.M22 = 443520 :=
      rfl
    rw [h, e22]
  exact not_weakExc_of_isD4two lieOrderBridge_holds hM22 h4

theorem d4TwoNormalizes_holds
    (G : Type) [Group G] [Finite G] : D4TwoNormalizes G := by
  intro X B L hX hB hBX hr hL hD4
  by_contra hnL
  have hw : catalogIs (PSimple 3 L) weakExcIndex :=
    weakExc_of_not_normalizes tables112_holds tableL2_unconditional tables112Types_holds
      tables112More_holds hX hB hBX hr hL hnL
  exact isD4two_not_weakExc hD4 hw

end Certified

end CFSG.LocalAnalysis.GLTheoremA.D4T
