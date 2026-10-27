module

public import CFSG.LieType.ChevTwo.OutData
public import CFSG.LieType.ChevTwo.BorelTitsTwo
public import CFSG.LieType.ChevTwo.OppCl.Main
public import CFSG.LieType.ChevTwo.OppositeFixedExc
import CFSG.LieType.ChevTwo.Reductions
import CFSG.LieType.ChevTwo.ReductionsTits

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.AGLEmbedding (IsClassicalTwoOrG2)

open CFSG.HardMathSupport.Cooperstein.StructureLie (OutTwoRank)


section OutCerts

theorem chev2OutTwoNilp_of_leaves : Chev2OutTwoNilp := fun _ _ _ hs hna hC =>
  (isChevTwo_iff.1 hC).elim (outTwoNilp_of_isClassicalTwoOrG2 hs hna)
    (outTwoNilp_of_isChevTwoExc hs hna)

theorem chev2OutTwoRank_of_leaves
    (hcl : ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → OutTwoRank Y) :
    Chev2OutTwoRank := fun _ _ _ hs hna hC =>
  (isChevTwo_iff.1 hC).elim (hcl _) (outTwoRank_of_isChevTwoExc hs hna)

end OutCerts

section CoreCerts

theorem chev2CoreCent_of_leaves : Chev2CoreCent := by
  intro S _ _ hs hna hC p hp hp2 R hR
  refine pCoreOf_autCentralizer_eq_bot_of_opp_tits (holdsTits_two_of_isChevTwo hs hna hC) ?_ p hp
    hp2 R hR
  exact (isChevTwo_iff.1 hC).elim (OppCl.oppositeFixed_top hs hna)
    (oppositeFixed_of_isChevTwoExc hs hna)

end CoreCerts

end CFSG.LieType.ChevTwo
