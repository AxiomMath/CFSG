module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineSocle
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleHS
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleLy
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleON
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleTits
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleFi24
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.DetCatalog

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.AGL81I.Section3 (ThreeNineHyp)

theorem kFactThreeNineSocle_of_bridges
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hbr : CFSG.Quasithin.B113KDet.CatalogBridge) : KFactThreeNineSocle := by
  intro X _ _ K E D X₁ p d h hDK hc
  rcases hc with ⟨rfl, rfl, hK, -⟩ | ⟨rfl, rfl, hK, -⟩ | ⟨rfl, rfl, hK, hT⟩ | ⟨rfl, rfl, hK, -⟩ |
    ⟨rfl, rfl, hK, -⟩
  · exact ThreeNineHyp.socle_of_tits h hK hDK
  · exact ThreeNineHyp.socle_of_hs h hK hDK
  · exact ThreeNineHyp.socle_of_ly h hK hDK hT
  · exact ThreeNineHyp.socle_of_onan h hK hDK
  · exact ThreeNineHyp.socle_of_fi24Prime hb hOrd hbr h hK hDK

theorem kFactThreeNineSocle_holds :
    KFactThreeNineSocle :=
  kFactThreeNineSocle_of_bridges CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.Quasithin.B113KDet.catalogBridge_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
