module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

@[expose] def m23KGens1 : List (Equiv.Perm (Fin 23)) :=
  tabWords [tab m23PermA, tab m23PermB] m23CentWords1

@[expose] def m23UGens1 : List (Equiv.Perm (Fin 23)) :=
  tabWords m23KGens1 [[3, 3, 3], [2, 3, 2, 3], [1, 3, 3, 3, 1], [1, 3, 1, 3, 1, 3]]

end CFSG.ClassicalInvolution
