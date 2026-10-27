module

public import CFSG.Sporadic.Schreier.LyBFS
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Data

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.LySchreier

abbrev Y3 : Type := Fin 256 × Fin 256 × Fin 256

@[expose] def imgTab (cs : List ℕ) : List ℕ := (List.range 256).map (applyCols 8 cs)

@[expose] def imgFin (tab : List ℕ) (c : Fin 256) : Fin 256 := Fin.ofNat 256 (tab.getD c.val 0)

@[expose] def mapX (t : Y3) : Y3 :=
  (imgFin (imgTab B1c) t.1, imgFin (imgTab B1c) t.2.1, imgFin (imgTab B1c) t.2.2)

@[expose] def mapY (t : Y3) : Y3 :=
  (imgFin (imgTab B2c) t.1, imgFin (imgTab B2c) t.2.1, imgFin (imgTab B2c) t.2.2)

@[expose] def rootY3 : Y3 := (1, 50, 100)

@[expose] def orbitList : List Y3 := bfsList [mapX, mapY] rootY3 22680

@[expose] def T1c : List ℕ := [1, 2, 10, 15]

@[expose] def T2c : List ℕ := [9, 1, 5, 2]

@[expose] def glList : List (List ℕ) := bfsList [mulCols 4 T1c, mulCols 4 T2c] (idCols 4) 20160

@[expose] def invCode (cs : List ℕ) : Bool :=
  (List.range 15).all fun s => applyCols 4 cs (s + 1) != 0

@[expose] def allMat4 : List (List ℕ) :=
  (List.range 16).flatMap fun a => (List.range 16).flatMap fun b =>
    (List.range 16).flatMap fun c => (List.range 16).map fun d => [a, b, c, d]

@[expose] def GLFacts : Bool :=
  glList.length == 20160 && allMat4.all (fun cs => !invCode cs || glList.contains cs) &&
    (List.range 15).all fun s => glList.any fun cs => cs.getD 0 0 == s + 1

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
