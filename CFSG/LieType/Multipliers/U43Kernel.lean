module

public import CFSG.LieType.Multipliers.U43Data

public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.CosetTable

abbrev coverWs : List (List (Fin 2 × Bool)) := coverWords rels fun i => commWords (coverPairs i)

@[expose] noncomputable def zk (k : ℕ) : PG 2 coverWs := PresentedGroup.mk _ (FreeGroup.mk (rels.getD k []))

end CFSG.LieType.Multipliers.U43
