module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Fischer.Classification.PartIII.Beta.Data

public section

namespace CFSG.LieType.Multipliers.U42

open CFSG.Fischer.Classification.Beta CFSG.Sporadic.Th.Native

@[expose] def relZ : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false),
    (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]

@[expose] def rels : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true), (1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true)],
    [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false),
      (0, true), (1, true), (0, false), (1, false)],
    relZ]

@[expose] def coverPairs : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 =>
    [([(1, false), (0, true), (1, true), (1, true), (0, true)],
        [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false),
          (1, false), (0, true), (1, false), (1, false)]),
      ([(0, true), (1, false), (0, true)], [(1, false), (1, false)])]
  | 1 =>
    [([(0, true), (1, false)],
        [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
          (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)]),
      ([(1, true), (1, true)], [(0, true), (1, true), (0, true)])]

@[expose] def checkWords : List (List (ℕ × Bool)) :=
  (rels ++ [commWords (coverPairs 0) ++ [(0, false)], commWords (coverPairs 1) ++ [(1, false)]]).map
    (List.map fun l : Fin 2 × Bool => (l.1.val, l.2))

@[expose] def bIdx : List (Fin 45) := [31, 5, 36, 44]

@[expose] def tauFun (i j : Fin 45) : Fin 45 := uIdx (tU (uPt i) (uPt j))

@[expose] def tauTab (i : Fin 45) : Table :=
  Array.ofFn fun j : Fin 45 => UInt32.ofNat (tauFun i j).val

@[expose] def seqTab (l : List (Fin 45)) : Table :=
  l.foldr (fun i T => compT 45 (tauTab i) T) (idT 45)

@[expose] def seqFun (l : List (Fin 45)) (j : Fin 45) : Fin 45 :=
  l.foldr (fun i k => tauFun i k) j

@[expose] def letterFun (l : ℕ × Bool) (j : Fin 45) : Fin 45 :=
  if l.1 = 0 then tauFun 0 j else if l.2 then seqFun bIdx j else seqFun bIdx.reverse j

@[expose] def applyWord (v : List (ℕ × Bool)) (j : Fin 45) : Fin 45 :=
  v.foldr letterFun j

@[expose] def witList : List (List (ℕ × Bool)) :=
  [[],
    [(1, false)],
    [(0, true), (1, false)],
    [(0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, false), (1, false)],
    [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (1, true)],
    [(0, true), (1, false), (0, true), (1, false), (1, false)],
    [(1, false), (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false),
      (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, false), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(1, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (0, true), (1, true)],
    [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(1, true), (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true),
      (1, true), (1, true)],
    [(1, false), (1, false)],
    [(0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true),
      (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, false)],
    [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(0, true), (1, false), (1, false)],
    [(1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false),
      (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
      (1, true)],
    [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (1, false)],
    [(1, false), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(1, true)],
    [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, true), (1, true)],
    [(1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, true), (0, true), (1, true), (1, true)],
    [(0, true), (1, true)],
    [(1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, true), (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true),
      (1, true)]]

@[expose] def wit (j : Fin 45) : List (ℕ × Bool) := witList.getD j.val []

end CFSG.LieType.Multipliers.U42
