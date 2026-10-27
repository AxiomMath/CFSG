module

public import Mathlib.Data.Int.Notation

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.TitsSec8

@[expose] def titsSec8ZWords : List (List ℤ) :=
  [[3, 13, 3, 13], [-13, -3, 13, 4, -13], [-13, -13, 4, -13], [4, -13, 4, 3, -13]]

@[expose] def titsSec8TWords : List (List ℤ) :=
  [[4, 4, -13, 4, 4, 13],
    [-13, -4, -4, -13, -1, -1, -1, -1, -1, -2, -1, -1, -1, -1, -2, -2],
    [-13, -4, 3, 3, -4, -4, -13, -4, 3, 3], [-3, -3, 4, 4, 4, 13, 13]]

end CFSG.ComponentClassification.RankTwoExceptional.TitsSec8
