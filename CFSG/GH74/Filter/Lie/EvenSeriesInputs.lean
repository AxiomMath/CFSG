module

public import CFSG.GH74.Filter.Lie.SepWitness

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SectionRank

@[expose] def witnessF4five : SepWitness .F4 5 where
  word := ![([1] : List (Fin 4)), ([2] : List (Fin 4)), ([2, 3, 1] : List (Fin 4)),
    ([2, 1] : List (Fin 4)), ([1, 2, 1] : List (Fin 4))]
  simple := ![(2 : Fin 4), (1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4)]
  sep := ![([2, 1] : List (Fin 4)), ([1, 2] : List (Fin 4)), ([2, 1, 2, 3, 2] : List (Fin 4)),
    ([1, 2, 0] : List (Fin 4)), ([1, 2, 0, 1, 0] : List (Fin 4))]

@[expose] def witnessE6five : SepWitness .E6 5 where
  word := ![([] : List (Fin 6)), ([5] : List (Fin 6)), ([5, 4] : List (Fin 6)),
    ([5, 4, 3] : List (Fin 6)), ([] : List (Fin 6))]
  simple := ![(5 : Fin 6), (4 : Fin 6), (3 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  sep := ![([5] : List (Fin 6)), ([5, 4] : List (Fin 6)), ([5, 4, 3] : List (Fin 6)),
    ([5, 4, 3, 1] : List (Fin 6)), ([0] : List (Fin 6))]

@[expose] def witnessE7five : SepWitness .E7 5 where
  word := ![([] : List (Fin 7)), ([] : List (Fin 7)), ([] : List (Fin 7)), ([] : List (Fin 7)),
    ([3, 4, 2, 3] : List (Fin 7))]
  simple := ![(6 : Fin 7), (4 : Fin 7), (2 : Fin 7), (1 : Fin 7), (1 : Fin 7)]
  sep := ![([6] : List (Fin 7)), ([4] : List (Fin 7)), ([2] : List (Fin 7)), ([1] : List (Fin 7)),
    ([3, 4, 2, 3, 1, 3, 2, 4, 3] : List (Fin 7))]

@[expose] def witnessE8five : SepWitness .E8 5 where
  word := ![([] : List (Fin 8)), ([] : List (Fin 8)), ([] : List (Fin 8)), ([] : List (Fin 8)),
    ([3, 4, 2, 3] : List (Fin 8))]
  simple := ![(7 : Fin 8), (4 : Fin 8), (2 : Fin 8), (1 : Fin 8), (1 : Fin 8)]
  sep := ![([7] : List (Fin 8)), ([4] : List (Fin 8)), ([2] : List (Fin 8)), ([1] : List (Fin 8)),
    ([3, 4, 2, 3, 1, 3, 2, 4, 3] : List (Fin 8))]

end CFSG.GH74.Filter.Lie
