module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporCentCo2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporCentRu
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMcL
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHe
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHS
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporON
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporJ4
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporFi24

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)

theorem threeNineFiveSporExtra_of_bridges (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hbr : CFSG.Quasithin.B113KDet.CatalogBridge) :
    ThreeNineFiveSporExtra := by
  intro X _ _ K E D X₁ p d s h hps hs
  rcases hps with ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact (h.false_of_mcl hs).elim
  · exact h.conclusion_of_hs hs
  · exact (h.false_of_co2 hs).elim
  · exact (h.false_of_co3 hs).elim
  · exact (h.false_of_ru hs).elim
  · exact (h.false_of_he hs).elim
  · exact h.conclusion_of_onan hs
  · exact h.conclusion_of_fi24Prime hb hOrd hbr hs
  · exact (h.false_of_j4 hs).elim

end CFSG.LocalAnalysis.AGL81I.Section3
