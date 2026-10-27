module

public section

namespace CFSG.LargeExtraspecial.AS62

@[expose] def relsB : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true)],
   [(2, true), (2, true)],
   [(3, true), (3, true), (3, true)],
   [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
   [(0, true), (1, true), (0, false), (1, false)],
   [(0, true), (2, true), (0, false), (2, false)],
   [(0, true), (3, true), (0, false), (3, false)],
   [(1, true), (3, true), (1, false), (3, false)],
   [(1, true), (2, true), (1, true), (2, true), (1, false), (2, false), (1, false), (2, false)],
   [(0, true), (1, true), (2, true), (1, true), (2, true), (3, true), (2, true), (1, true),
    (2, true), (3, false), (3, true), (3, true), (2, true), (1, true), (2, true), (3, false),
    (3, false)]]

@[expose] def liftWord (w : List (Fin 4 × Bool)) : List (Fin 5 × Bool) :=
  w.map fun l => (l.1.castSucc, l.2)

@[expose] def rels1Extra : List (List (Fin 5 × Bool)) :=
  [[(4, true), (4, true), (4, true)],
   [(3, true), (4, true), (3, false), (4, false)],
   [(1, true), (4, true), (1, true), (4, true)],
   [(4, true), (1, true), (2, true), (1, true), (2, true), (4, false), (2, true), (0, true)]]

@[expose] def rels1 : List (List (Fin 5 × Bool)) :=
  relsB.map liftWord ++ rels1Extra

@[expose] def rels2Extra : List (List (Fin 5 × Bool)) :=
  [[(4, true), (4, true)],
   [(4, true), (3, true), (4, true), (3, true)],
   [(4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true),
    (4, true), (2, true)],
   [(4, true), (3, true), (2, true), (4, true), (3, true), (2, true), (4, true), (3, true),
    (2, true)],
   [(4, true), (0, true), (4, true), (1, false)]]

@[expose] def rels2 : List (List (Fin 5 × Bool)) :=
  relsB.map liftWord ++ rels2Extra

end CFSG.LargeExtraspecial.AS62
