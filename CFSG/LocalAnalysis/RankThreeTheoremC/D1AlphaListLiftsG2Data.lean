module

public import CFSG.LieType.Multipliers.G23Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift

open CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native

@[expose] def parseRoots (s : String) : List (Fin 4) :=
  s.toList.filterMap fun c =>
    if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2
    else if c = '3' then some 3 else none

@[expose] def wY : Fin 3 → List (Fin 4)
  | 0 => parseRoots "113323323321"
  | 1 => parseRoots "113322332233221"
  | 2 => parseRoots "322322322"

@[expose] def wInv : Fin 3 → List (Fin 4)
  | 0 => parseRoots "300122332231100"
  | 1 => parseRoots "300122332231100"
  | 2 => parseRoots "0133233221003"

@[expose] def wSw : Fin 3 → Fin 3 → List (Fin 4)
  | 0, 1 => parseRoots "33113311"
  | 0, 2 => parseRoots "31302033223"
  | 1, 2 => parseRoots "1102033223"
  | _, _ => []

@[expose] def rootArrs : Array (Array (Array ℕ)) := #[rootArr 0, rootArr 1, rootArr 2, rootArr 3]

@[expose] def wordM (w : List (Fin 4)) : Array (Array ℕ) :=
  w.foldr (fun j M => mulM 3 14 (rootArrs[j.val]!) M) (idM 14)

@[expose] def wpow (w : List (Fin 4)) (k : ℕ) : List (Fin 4) := (List.replicate k w).flatten

@[expose] def wMono (a b c : ℕ) : List (Fin 4) :=
  wpow (wY 0) a ++ wpow (wY 1) b ++ wpow (wY 2) c

@[expose] def eqPairs : List (List (Fin 4) × List (Fin 4)) :=
  (List.finRange 3).map (fun i => (wY i ++ wY i ++ wY i, [])) ++
  (List.finRange 3).flatMap (fun i =>
    (List.finRange 3).map fun j => (wY i ++ wY j, wY j ++ wY i)) ++
  (List.finRange 3).map (fun i => (wInv i ++ wY i, wY i ++ wY i ++ wInv i)) ++
  [(0, 1), (0, 2), (1, 2)].flatMap (fun (p : Fin 3 × Fin 3) =>
    [(wSw p.1 p.2 ++ wY p.1, wY p.2 ++ wSw p.1 p.2),
      (wSw p.1 p.2 ++ wY p.2, wY p.1 ++ wSw p.1 p.2)])

@[expose] def nePairs : List (List (Fin 4)) :=
  ((List.range 3).flatMap fun a => (List.range 3).flatMap fun b => (List.range 3).map fun c =>
    (a, b, c)).filter (fun t => t != (0, 0, 0)) |>.map fun t => wMono t.1 t.2.1 t.2.2

@[expose] def neOne (A : Array (Array ℕ)) : Bool :=
  (List.range 14).any fun i => (List.range 14).any fun j =>
    (A[i]!)[j]! % 3 != (if i = j then 1 else 0)

@[expose] def liftCheck : Bool :=
  eqPairs.all (fun p => wordM p.1 == wordM p.2) && nePairs.all (fun w => neOne (wordM w))

end CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift
