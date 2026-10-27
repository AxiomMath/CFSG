module

public import CFSG.GH74.Generic.BProg.B1.Stage3aRankJ1
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankRee

public section

namespace CFSG.GH74.Generic.BProg.B1

theorem noJPrime_of_shape3SD
    (hSD : NoJPrimeShape3SD) : NoJPrimeFor QShapeNS :=
  noJPrime_of_shapes noJPrimeFor_shape1 (noJPrimeFor_shape3_of_SD hSD) noJPrimeFor_shape4
    noJPrimeFor_shape5

end CFSG.GH74.Generic.BProg.B1
