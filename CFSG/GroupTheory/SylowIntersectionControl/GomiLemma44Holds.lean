module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma44
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact34Holds
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37TripleA7
import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.GroupTheory

theorem gomiLemma44_holds : GomiLemma44 :=
  gomiLemma44_of_facts CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    gomiFact34_holds fun _ _ _ hW _ _ _ hH hJ => not_tripleA7_of_gomiFact37Hyp hW hH hJ

end CFSG.GroupTheory
