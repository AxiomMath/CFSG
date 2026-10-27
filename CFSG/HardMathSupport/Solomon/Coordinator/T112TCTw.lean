module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCHolds
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem timmesfeldSporadicMultipliers_of_census
    (h : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) :
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
  ⟨fun s => by rw [h.1 s]; cases s <;> rfl, h.2⟩

section Certs


theorem tables112Types_of_tw
    (hTw : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6RankLowerTw) : Tables112Types :=
  tables112Types_of_multipliers
    (timmesfeldSporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) hTw

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator
