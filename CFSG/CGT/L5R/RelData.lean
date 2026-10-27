module

public import CFSG.CGT.M24R.RelData

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.M24R

@[expose] def thetaRelsL : List M24Word :=
  [[(10, true), (10, true)],
   [(10, true), (0, true), (1, true), (2, true), (5, false), (4, true), (10, true), (4, false),
    (5, true), (2, false), (1, false), (0, false)],
   [(10, true), (5, true), (4, true), (3, true), (0, false), (8, true), (10, true), (8, false),
    (2, false), (4, true), (1, false), (3, false)]]

@[expose] def ruRelL : List M24Word :=
  [[(10, true), (0, true), (9, true), (10, true), (9, false), (0, false), (10, true), (3, false),
    (5, false), (1, false), (0, false), (2, false), (4, false), (1, false), (0, false)]]

@[expose] def l52Rels : List M24Word := relsN8 ++ thetaRelsL ++ ruRelL

@[expose] def l52M : Fin 11 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 1, 1, 1, 0; 1, 1, 0, 1, 0; 1, 1, 1, 0, 0; 1, 0, 1, 1, 0; 0, 0, 0, 0, 1],
    !![0, 1, 1, 1, 0; 0, 1, 1, 0, 0; 0, 1, 0, 0, 0; 1, 1, 0, 1, 0; 0, 0, 0, 0, 1],
    !![0, 1, 0, 1, 0; 1, 0, 1, 1, 0; 1, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 1, 0, 0; 1, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 1, 1, 0; 0, 0, 0, 0, 1],
    !![0, 0, 1, 0, 0; 1, 1, 1, 1, 0; 1, 0, 1, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 1, 1],
    !![1, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]]

@[expose] def dWordL : Fin 2 → M24Word :=
  ![[(0, true), (1, true), (2, true), (5, false), (4, true)],
    [(5, true), (4, true), (3, true), (0, false), (8, true)]]

@[expose] def thetaWordL : Fin 2 → M24Word :=
  ![[(0, true), (1, true), (2, true), (5, false), (4, true)],
    [(3, true), (1, true), (4, false), (2, true), (8, true)]]

@[expose] def nWordL : M24Word :=
  [(0, true), (9, true)]

@[expose] def wWordL : M24Word :=
  [(0, true), (1, true), (4, true), (2, true), (0, true), (1, true), (5, true), (3, true)]

@[expose] def bWordL : M24Word :=
  [(0, true), (1, true), (2, true), (3, true), (0, true), (4, true), (3, false), (5, true),
   (1, false), (7, true), (8, true)]

@[expose] def dAWordL : M24Word :=
  [(7, true), (8, true)]

@[expose] def yWordL : Fin 2 → M24Word :=
  ![[(2, true), (3, true), (4, false), (5, true), (3, false)],
    [(4, true), (1, true), (2, true), (0, true), (5, true), (3, true)]]

@[expose] def fWordL : Fin 2 → M24Word :=
  ![[(1, true), (0, true), (3, true), (5, false), (1, true)],
    [(5, true), (3, true), (0, true), (2, true), (1, true), (4, true)]]

@[expose] def transvWordL : Fin 20 → M24Word :=
  ![[(1, true), (0, true), (3, true), (4, true), (1, true), (5, true), (2, true), (4, true)],
    [(0, true), (1, true), (3, true), (4, true), (5, true), (1, true), (3, true), (2, true)],
    [(0, true), (1, true), (5, true), (2, true), (0, true), (1, true), (3, true), (4, true)],
    [(10, true)],
    [(0, true), (1, true), (2, true), (3, true), (0, true), (1, true), (4, true), (5, true)],
    [(0, true), (1, true), (3, true), (2, true), (0, true), (1, true), (5, true), (4, true)],
    [(0, true), (1, true), (2, true), (3, true), (4, true), (5, true), (2, true), (3, true)],
    [(0, true), (4, true), (10, true), (0, true), (4, true)],
    [(0, true), (1, true), (2, true), (5, true), (4, true), (1, true), (2, true), (3, true)],
    [(0, true), (2, true), (5, true), (3, true), (0, true), (2, true), (1, true), (4, true)],
    [(0, true), (1, true), (4, true), (3, true), (0, true), (1, true), (2, true), (5, true)],
    [(1, true), (0, true), (10, true), (0, false), (1, false)],
    [(0, true), (2, true), (1, true), (3, true), (0, true), (2, true), (5, true), (4, true)],
    [(0, true), (1, true), (3, true), (5, true), (4, true), (1, true), (3, true), (2, true)],
    [(0, true), (1, true), (2, true), (3, true), (0, true), (1, true), (4, true), (5, false),
     (4, true)],
    [(0, false), (10, true), (0, true)],
    [(6, true)],
    [(7, true)],
    [(8, true)],
    [(9, true)]]

@[expose] def transvPairL : Fin 20 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4),
    (3, 0), (3, 1), (3, 2), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3)]

end CFSG.CGT.L5R
