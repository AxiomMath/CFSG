module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23BaseInputs

public section

namespace CFSG.QuasithinUnique.A5.G3.M23

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def tau : Fin 23 → Fin 4 :=
  ![0, 3, 3, 3, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 2, 1, 1, 3, 3]

@[expose] def nxt : Fin 23 → Fin 23 :=
  ![0, 2, 3, 4, 6, 7, 8, 14, 9, 10, 11, 12, 13, 15, 18, 16, 17, 21, 5, 20, 19, 22, 1]

@[expose] def wd : Fin 23 → List ℕ :=
  ![[], [3,1], [0,1,0,3], [1,0], [3,0], [1,0], [3,1,3], [1], [0], [0,1,0,3], [0,2], [3],
    [0,2,3], [1], [1,0], [3,1], [3], [3], [1], [0], [0], [1], [3,0]]

end CFSG.QuasithinUnique.A5.G3.M23
