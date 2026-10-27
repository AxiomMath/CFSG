module

public import CFSG.LieType.Multipliers.U62Data
public import CFSG.LieType.Multipliers.CoverWords

@[expose] public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.CosetTable

abbrev coverWs : List (List (Fin 5 × Bool)) := coverWords rels fun i => commWords (coverPairs i)

end CFSG.LieType.Multipliers.U62
