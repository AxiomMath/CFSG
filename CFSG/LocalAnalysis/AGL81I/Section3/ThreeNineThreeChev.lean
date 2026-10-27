module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeChevSmall
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeL227
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreePSp43
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem threeNineThreeChev_holds :
    ThreeNineThreeChev := by
  intro X _ _ K E D X₁ d h hK
  rcases hK with hK | hK | hK | hK | hK
  · exact false_of_threeNineHyp_L29 h hK
  · exact false_of_threeNineHyp_L227 h hK
  · exact false_of_threeNineHyp_L33 h hK
  · exact false_of_threeNineHyp_U33 h hK
  · exact false_of_threeNineHyp_PSp43 h hK

end CFSG.LocalAnalysis.AGL81I.Section3
