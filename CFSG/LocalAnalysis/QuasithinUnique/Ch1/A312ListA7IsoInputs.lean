module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven
open Matrix Equiv

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def vec8 : Fin 7 → V3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![1, 1, 0], ![0, 1, 1], ![1, 0, 1]]

@[expose] def vec9 : Fin 7 → V3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![0, 1, 1], ![1, 1, 0], ![1, 0, 1]]

@[expose] def idxOf (vec : Fin 7 → V3) (v : V3) : Fin 7 :=
  if v = vec 0 then 0 else if v = vec 1 then 1 else if v = vec 2 then 2 else
  if v = vec 3 then 3 else if v = vec 4 then 4 else if v = vec 5 then 5 else 6

@[expose] def rhoRaw (vec : Fin 7 → V3) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : R7 :=
  ⟨idxOf vec (A *ᵥ vec 0), idxOf vec (A *ᵥ vec 1), idxOf vec (A *ᵥ vec 2), idxOf vec (A *ᵥ vec 3),
    idxOf vec (A *ᵥ vec 4), idxOf vec (A *ᵥ vec 5), idxOf vec (A *ᵥ vec 6)⟩

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
