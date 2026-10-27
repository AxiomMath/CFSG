module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Q8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
  Equiv

@[expose] def gW1 : Fin 5 → ZMod 2 := ![1, 0, 1, 1, 1]

@[expose] def gW1' : Fin 5 → ZMod 2 := ![0, 1, 1, 1, 1]

@[expose] def dA : RP := (gW1, Equiv.swap (0 : Fin 5) 1)

@[expose] def dB : RP := (0, Equiv.swap (0 : Fin 5) 1)

@[expose] def dtab : DihedralGroup 4 → RP
  | .r i => rpow dA i.val
  | .sr i => rmul dB (rpow dA i.val)

@[expose] def bv : Fin 4 → (Fin 5 → ZMod 2) :=
  ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 1, 0, 1], ![0, 0, 1, 1, 0]]

@[expose] def tv : Fin 4 → Perm (Fin 4) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

@[expose] def extP (g : Perm (Fin 4)) : Perm (Fin 5) := Equiv.Perm.decomposeFin.symm (0, g)

@[expose] def ptab (σ : Perm (Fin 4)) : RP := (bv (σ 0), extP (tv (σ 0) * σ))

@[expose] def vecF : Fin 4 → (Fin 5 → ZMod 2) := ![0, g1, gW1, gW1']

end CFSG.QuasithinUnique.A5
