module

public import CFSG.LieType.ChevTwo.OppositeFixedExcAssembly

public section

namespace CFSG.LieType.ChevTwo


theorem oppositeFixed_of_isChevTwoExc {S : Type} [Group S] [Finite S] (_hs : IsSimpleGroup S)
    (_hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevTwoExc S) : OppositeFixed S :=
  oppositeFixed_of_isChevTwoExc_cert h

end CFSG.LieType.ChevTwo
