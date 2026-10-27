module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

@[expose] def m22KGens1 : List (Equiv.Perm (Fin 22)) :=
  tabWords [tab m22gA, tab m22gB] m22CentWords1

@[expose] def m22UGens1 : List (Equiv.Perm (Fin 22)) :=
  tabWords m22KGens1 [[1, 1], [3, 3], [3, 2, 1]]

end CFSG.ClassicalInvolution
