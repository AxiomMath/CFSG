module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LieType.Multipliers.U62

@[expose] def rels : List (List (Fin 5 × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true)],
    [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false),
      (0, true), (1, true), (0, false), (1, false)],
    [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false),
      (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)],
    [(2, true), (2, true), (2, true)],
    [(2, true), (0, true), (2, false), (0, false)],
    [(2, true), (1, true), (2, false), (1, false)],
    [(3, true), (3, true)],
    [(3, true), (0, true), (3, true), (0, false)],
    [(3, true), (1, false), (0, true), (1, true), (3, true), (1, false), (0, false), (1, true)],
    [(3, true), (1, true), (1, true), (0, true), (1, false), (1, false), (3, true), (1, true),
      (1, true), (0, false), (1, false), (1, false)],
    [(3, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, false), (2, false),
      (3, true), (2, true), (1, true), (0, false), (1, false), (0, false), (1, true), (1, true)],
    [(3, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (2, false), (3, true), (2, false), (1, true), (1, true), (0, false),
      (1, true), (1, true), (0, false), (1, true)],
    [(3, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true), (0, true), (1, true), (1, true), (3, true), (1, false), (1, false), (0, false),
      (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false),
      (1, false)],
    [(3, true), (1, true), (0, true), (1, false), (3, true), (1, true), (0, true), (1, false),
      (3, true), (1, true), (0, true), (1, false)],
    [(4, true), (4, true)],
    [(4, true), (0, true), (4, false), (0, false)],
    [(4, true), (1, true), (4, false), (1, false)],
    [(4, true), (2, true), (4, true), (2, true)],
    [(4, true), (3, true), (4, true), (3, true), (4, true), (3, true)],
    [(4, true), (3, true), (1, false), (0, true), (4, true), (3, true), (1, false), (0, true),
      (4, true), (3, true), (1, false), (0, true), (4, true), (3, true), (1, false), (0, true),
      (4, true), (3, true), (1, false), (0, true), (4, true), (3, true), (1, false), (0, true),
      (4, true), (3, true), (1, false), (0, true)],
    [(4, true), (3, true), (2, true), (0, true), (1, false), (4, true), (3, true), (2, true),
      (0, true), (1, false), (4, true), (3, true), (2, true), (0, true), (1, false), (4, true),
      (3, true), (2, true), (0, true), (1, false), (4, true), (3, true), (2, true), (0, true),
      (1, false), (4, true), (3, true), (2, true), (0, true), (1, false), (4, true), (3, true),
      (2, true), (0, true), (1, false)]]

@[expose] def coverPairs : Fin 5 → List (List (Fin 5 × Bool) × List (Fin 5 × Bool))
  | 0 =>
    [([(0, true), (1, true), (1, true), (0, true), (1, false)],
          [(0, true), (1, false), (1, false), (0, true), (1, true), (1, true)]),
        ([(1, true), (0, true), (1, false), (1, false), (0, true), (1, false)],
          [(0, false), (1, false), (0, true), (1, false), (1, false), (0, true)])]
  | 1 =>
    [([(1, false), (0, true)],
          [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false)]),
        ([(0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
          [(1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true)])]
  | 2 =>
    [([(0, true)],
          [(1, true), (0, true), (1, true), (1, true)]),
        ([(0, true), (1, true), (3, true), (1, true)],
          [(1, true), (0, true), (1, false), (2, true)])]
  | 3 =>
    [([(0, true)],
          [(1, false), (0, true), (3, true), (1, true)]),
        ([(2, true), (3, true), (2, true)],
          [(1, true), (3, true), (1, false), (2, true)])]
  | 4 =>
    [([(0, true), (3, true), (1, true)],
          [(3, true), (1, true), (3, true), (2, true)]),
        ([(0, true), (1, true), (3, true)],
          [(1, true), (3, true), (4, true), (3, true)])]

@[expose] def genWord : Fin 5 → List ℤ
  | 0 => [-1]
  | 1 => [-4, -46, -18, 14, 46, 15]
  | 2 => [-22, -2, 1, 4, 8, -26]
  | 3 => [22]
  | 4 => [35]

@[expose] def xWord : List (Fin 5 × Bool) :=
  [(0, false), (1, false), (0, false), (1, true), (1, true), (3, true), (0, true), (1, true),
    (1, true), (0, true), (3, true), (1, false), (1, false), (3, true), (0, true), (1, false),
    (1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (3, false), (2, false), (3, false),
    (4, false), (3, false), (1, true), (3, false), (1, false), (3, false), (1, false), (1, false),
    (0, false)]

@[expose] def yWord : List (Fin 5 × Bool) :=
  [(0, false), (1, false), (0, false), (1, true), (1, true), (0, false), (3, false), (1, true),
    (1, true), (3, false), (0, false), (1, false), (1, false), (0, false), (3, false), (1, false),
    (0, false), (1, true), (1, true), (0, false), (1, true), (1, true), (0, false), (1, false),
    (3, false), (1, true), (3, false), (1, true), (0, false), (1, true), (1, true), (4, false),
    (3, false), (1, true), (3, false), (1, true), (1, true), (0, false), (1, false), (2, false),
    (3, false), (4, false)]

@[expose] def zWord : List (Fin 5 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false),
    (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]

@[expose] def kerThree : List (Fin 5 × Bool) := rels[19]!

@[expose] def kerTwo : List (Fin 5 × Bool) := rels[21]!

@[expose] def kerSix : List (Fin 5 × Bool) := rels[22]!

@[expose] def kerTwo' : List (Fin 5 × Bool) := kerSix ++ kerSix ++ kerSix

@[expose] def fixWords : List (List (Fin 5 × Bool)) :=
  [kerThree ++ kerThree ++ kerThree, kerTwo ++ kerTwo, kerTwo' ++ kerTwo']

@[expose] def moveWords : List (List (Fin 5 × Bool)) :=
  [kerThree, kerTwo, kerTwo', kerTwo ++ kerTwo']

end CFSG.LieType.Multipliers.U62
