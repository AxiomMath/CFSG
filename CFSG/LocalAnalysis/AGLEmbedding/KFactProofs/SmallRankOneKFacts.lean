module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary

public section

namespace CFSG.AGLEmbedding

theorem smallRankOneData_of_small {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hK : IsSmallLinTwo p K ∨ IsSmallUnitary p K) (T : Sylow p K) :
    SmallRankOneData p K T := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rcases hK with hK | hK
  · exact smallRankOneData_of_isSmallLinTwo hp2 hK T
  · exact smallRankOneData_of_isSmallUnitary hp hK T

theorem kFactSmallBorelSolvable : KFactSmallBorelSolvable := by
  intro K _ _ p hp h5 hK T
  exact isSolvable_glbCore_of_data hp (smallRankOneData_of_small hp h5 hK T)

theorem kFactOneLieSmallLie : KFactOneLieSmallLie := by
  intro K _ _ p hp h5 hK T
  exact oneLieFacts_of_data hp (fun T' => smallRankOneData_of_small hp h5 hK T') T

end CFSG.AGLEmbedding
