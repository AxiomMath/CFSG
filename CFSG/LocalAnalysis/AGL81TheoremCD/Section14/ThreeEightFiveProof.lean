module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveReduce
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveOrder
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeEightFiveFive

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem kFactThreeEightFive_holds :
    KFactThreeEightFive := by
  refine kFactThreeEightFive_of_centralizerHasPElementOutside
    (fun q hq hq2 _ _ h => prime_dvd_card_of_nineFourListGroup hq hq2 h) ?_
  intro q hq hq2 X _ _ hO h2 hF N hN
  have h4 : q ≠ 4 := by
    rintro rfl
    norm_num at hq
  rcases (by have := hq.two_le; omega : q = 3 ∨ 5 ≤ q) with rfl | hq5
  · exact ThreeEightFive.centralizerHasPElementOutside_three_of_nineFourListGroup hO h2 hF hN
  · exact (ThreeEightFive.good_of_nineFourListGroup_of_five_le hq hq5 hO h2 hF hN).2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
