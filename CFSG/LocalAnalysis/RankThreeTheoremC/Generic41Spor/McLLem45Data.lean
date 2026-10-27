module

public import Certificates.Data.MaxD2Heis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45

open Certificates.MaxD2Perm Certificates.MaxD2Heis CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

@[expose] def wordW : List Int := [
    -2, -1, 2, 1, -1, -1, -1, -2, 2, -1, -1, -1, 1, 2, -1, 2, 2, 2, 2, -1,
    -2, -2, -1, -1, -2, -2, 1, 2, 2, -2, 2, 2, -1, 2, 2, 1, -1, -2, 1, 2,
    1, -2, -1, 2, 1, -1, -2, -2, 1, -2, -2, 2, -2, -2, -1, 2, 2, 1, 1, 2,
    2, 1, -2, -2, -2, -2, 1, -2, -1, 1, 1, 1, -2, 2, 1, 1, 1, -1, -2, 1,
    2]

@[expose] def tree : List (Nat × Nat) := [
    (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 7), (1, 1), (1, 2), (1, 3),
    (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 7), (3, 1), (3, 2), (3, 3),
    (3, 5), (3, 6), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 3), (5, 7),
    (6, 1), (6, 5), (6, 6), (6, 7), (7, 1), (7, 2), (7, 6), (7, 7), (8, 1),
    (8, 3), (8, 7), (9, 2), (9, 5), (10, 3), (10, 5), (10, 7), (11, 1), (11, 2),
    (11, 5), (11, 6), (12, 1), (12, 2), (12, 3), (12, 6), (12, 7), (13, 3), (13, 7),
    (14, 3), (14, 5), (15, 1), (15, 2), (15, 5), (15, 6), (15, 7), (16, 3), (16, 6),
    (17, 1), (17, 3), (17, 7), (20, 3), (20, 5), (20, 7), (21, 1), (21, 2), (21, 3),
    (21, 7), (22, 2), (23, 2), (24, 7), (26, 1), (26, 2), (26, 3), (26, 5), (27, 7),
    (30, 3), (31, 6), (32, 1), (32, 2), (32, 6), (33, 1), (33, 2), (33, 7), (34, 3),
    (34, 7), (35, 6), (36, 1), (36, 3), (36, 7), (37, 1), (37, 5), (37, 6), (38, 1),
    (38, 7), (39, 2), (39, 3), (41, 5), (41, 6), (42, 6), (43, 1), (45, 3), (45, 7),
    (48, 1), (48, 2), (51, 3), (56, 6), (60, 3), (64, 3), (66, 5), (74, 1), (83, 6),
    (84, 2), (87, 2)]

@[expose] def orbitStep (D : Data) (L : Array Tab) (pg : Nat × Nat) : Array Tab :=
  let x := L[pg.1]!
  let ng := (nGens D).size
  let gt := if pg.2 < ng then (nGens D)[pg.2]! else (nGensI D)[pg.2 - ng]!
  let gi := if pg.2 < ng then (nGensI D)[pg.2]! else (nGens D)[pg.2 - ng]!
  L.push (conjTab D.n gt gi x)

@[expose] def orbitList (D : Data) (tr : List (Nat × Nat)) : Array Tab :=
  tr.foldl (orbitStep D) #[wT D D.uW]

@[expose] def treeOK (D : Data) (tr : List (Nat × Nat)) : Bool :=
  allBelow tr.length fun k => decide ((tr[k]!).1 < k + 1) && decide ((tr[k]!).2 < 2 * (nGens D).size)

@[expose] def wConj (D : Data) (u w : Tab) (k : Nat) : Tab :=
  comp D.n (comp D.n (powT D.n u k) w) (powT D.n u (5 - k))

@[expose] def check (D : Data) (w : List Int) (tr : List (Nat × Nat)) : Bool :=
  let u := wT D D.uW
  let v := wT D D.vW
  let wt := wT D w
  let one := idTab D.n
  let L := orbitList D tr
  (powT D.n u 5 == one) && !(comp D.n u v == comp D.n v u) && (comp D.n wt wt == one) &&
    (allBelow 5 fun k => allBelow 5 fun l =>
      comp D.n (wConj D u wt k) (wConj D u wt l) == comp D.n (wConj D u wt l) (wConj D u wt k)) &&
    !(wConj D u wt 1 == wConj D u wt 0) && treeOK D tr &&
    (allBelow (hrEnum D).tabs.size fun i =>
      (zTabs D).any (· == (hrEnum D).tabs[i]!) || L.any (· == (hrEnum D).tabs[i]!))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45
