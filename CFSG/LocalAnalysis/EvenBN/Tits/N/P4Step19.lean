module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W5

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Final19


theorem step19_holds : Step19 := by
  intro G _ _ d z₀ h49 hd hz h09 h10 _ h17s h17 h18
  exact ⟨P4.node19_card h49 hd hz h09 h10 h17s h17 h18, P4.node19_conj2 h49 hd hz h09 h10 h17s h17 h18,
    P4.node19_conj3 h49 hd hz h10 h17 h18, P4.node19_conj4 h49 hd hz h10 h17 h18,
    P4.node19_conj5 h49 hd hz h09 h10 h17s h17 h18⟩

end Final19

end CFSG.LocalAnalysis.EvenBN.Tits.N
