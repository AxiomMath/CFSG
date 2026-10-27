module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

@[expose] def m12KGens1 : List (Equiv.Perm (Fin 12)) :=
  tabWords [tab m12gA, tab m12gB] m12CentWords1

@[expose] def m12KGens2 : List (Equiv.Perm (Fin 12)) :=
  tabWords [tab m12gA, tab m12gB] m12CentWords2

@[expose] def m12UGens1 : List (Equiv.Perm (Fin 12)) :=
  tabWords m12KGens1 [[1], [3, 3], [2, 4, 3], [4, 3, 2], [2, 2, 3, 4]]

@[expose] def m12NGens2 : List (Equiv.Perm (Fin 12)) :=
  tabWords m12KGens2 [[1], [3]]

end CFSG.ClassicalInvolution
