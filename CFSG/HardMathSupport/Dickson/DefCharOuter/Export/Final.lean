module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.All
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Exceptional
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcCarrier
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthAssembly
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Chev
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4ThreeCent
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ChevPBal

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Solomon.Coordinator

section KData


theorem outerCentAll_of_D4 (hD4 : D4ThreeOuterCent) : OuterCentAll :=
  outerCentAll_of ⟨carrierOn_exceptional, outerCentOn_exceptional⟩
    ⟨carrierOn_symplecticOrthogonal, outerCentOn_symplecticOrthogonal_of_D4 hD4⟩

theorem kdOutChev_of_D4 (hD4 : D4ThreeOuterCent) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KDOutChev p :=
  kdOutChev_of_outerCent (outerCentAll_of_D4 hD4) hp hp2

theorem kdOutChevUnique_of_D4 (hD4 : D4ThreeOuterCent) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KDOutChevUnique p :=
  kdOutChevUnique_of_outerCent (outerCentAll_of_D4 hD4) hp hp2

theorem kdOutCoreFree_of_D4 (hD4 : D4ThreeOuterCent) : KDOutCoreFree :=
  kdOutCoreFree_of_outerCent (outerCentAll_of_D4 hD4)

theorem kdOutCentInner_of_D4 (hD4 : D4ThreeOuterCent) : KDOutCentInner :=
  kdOutCentInner_of_outerCent (outerCentAll_of_D4 hD4)

theorem outerCentAll_of_graphCent (hG : D4ThreeGraphCent) : OuterCentAll :=
  outerCentAll_of_D4 (d4ThreeOuterCent_of_graphCent hG)

theorem kdOutChev_of_graphCent (hG : D4ThreeGraphCent) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KDOutChev p :=
  kdOutChev_of_D4 (d4ThreeOuterCent_of_graphCent hG) hp hp2

theorem kdOutChevUnique_of_graphCent (hG : D4ThreeGraphCent) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : KDOutChevUnique p :=
  kdOutChevUnique_of_D4 (d4ThreeOuterCent_of_graphCent hG) hp hp2

theorem outerCentAll_holds : OuterCentAll :=
  outerCentAll_of_graphCent d4ThreeGraphCent_holds

theorem kdOutChev_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KDOutChev p :=
  kdOutChev_of_graphCent d4ThreeGraphCent_holds hp hp2

theorem kdOutChevUnique_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : KDOutChevUnique p :=
  kdOutChevUnique_of_graphCent d4ThreeGraphCent_holds hp hp2

theorem kdOutCoreFree_holds : KDOutCoreFree :=
  kdOutCoreFree_of_outerCent outerCentAll_holds

theorem kdOutCentInner_holds : KDOutCentInner :=
  kdOutCentInner_of_outerCent outerCentAll_holds

end KData

section ChevPBal


theorem i271ChevPBal_of_D4 (hD4 : D4ThreeOuterCent) : I271ChevPBal :=
  i271ChevPBal_of_outerCent (outerCentAll_of_D4 hD4)

theorem i271ChevPBal_of_graphCent (hG : D4ThreeGraphCent) : I271ChevPBal :=
  i271ChevPBal_of_D4 (d4ThreeOuterCent_of_graphCent hG)

theorem i271ChevPBal_holds : I271ChevPBal :=
  i271ChevPBal_of_graphCent d4ThreeGraphCent_holds

end ChevPBal

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
