module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftReduce
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftList
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftUnitary
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftMcL

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem kFactCentralLift_holds :
    KFactCentralLift := by
  refine kFactCentralLift_of_quotient ?_
  intro q p hq hq2 hp hp2 _ X _ _ K hK hlist hodd hqZ hpZ b hbN hb hbC H hH hS
  obtain ⟨rfl, hZ, hcase⟩ := CentralLift.centralLift_cases hq hq2 hp hp2 hK hlist hodd hqZ hpZ
  rcases hcase with ⟨d, Q, hd, hQq, h3, ⟨e⟩⟩ | ⟨rfl, ⟨e⟩⟩
  · exact CentralLift.not_le_of_unitary hq hq2 K hK d Q hd hQq h3 e hZ hbN hb hH hS
  · exact CentralLift.not_le_of_mcl K hK e hZ hbN hb hbC hH hS

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
