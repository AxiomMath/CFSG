module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL6Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

@[expose] def uWord : List Int := [2, 3, 4]

@[expose] def aWords : List (List Int) := [cWord, [1, 3], [2, 4], [5]]

@[expose] def vWords : List (List Int) := [cWord, [1, 3], [2, 4], [6]]

@[expose] def hWord : List Int := [-8, 7, 8]

@[expose] def l7Fusion (nE : Array Table) (good : List Table) (eT uT : Table)
    (LE : List Table) : Bool :=
  let ueT := compT 16 uT eT
  let goodE := LE.filter (memTab 16 good)
  goodE.length == 56 && tsubOK goodE.toArray 128 &&
    memTab 16 good uT && memTab 16 good ueT && memTab 16 LE uT && memTab 16 LE ueT &&
    commTT 16 eT uT &&
    LE.all fun T => !memTab 16 good T || conjIn nE eT T || conjIn nE uT T || conjIn nE ueT T

@[expose] def l7Sylow (cT eT uT : Table) (LE LS : List Table) : Bool :=
  let ueT := compT 16 uT eT
  let ecT := compT 16 eT cT
  let LT := LS.filter (commTT 16 eT)
  let LR := LE.filter (commTT 16 eT)
  LT.length == 128 && LR.length == 64 &&
    LT.all (fun y => !LT.all (commTT 16 y) || tblEq 16 y (idT 16) || tblEq 16 y eT ||
      tblEq 16 y cT || tblEq 16 y ecT) &&
    LR.all (fun y => !LR.all (commTT 16 y) || tblEq 16 y (idT 16) || tblEq 16 y eT ||
      tblEq 16 y cT || tblEq 16 y ecT) &&
    LT.all (fun y => memTab 16 LE y || !sqIn 16 cT y ||
      decide (2 * (LE.filter fun x => commTT 16 eT x && commIn 16 cT x y).length < 64)) &&
    [uT, ueT].all fun x =>
      (LS.filter (commTT 16 x)).length == 128 && (LE.filter (commTT 16 x)).length == 64

@[expose] def l7A (bad : List Table) (cT : Table) (gA : Array Table) (LE LS : List Table) : Bool :=
  let LA := (tenum gA).toList
  tsubOK gA 16 &&
    LA.all (fun a => LA.all fun b => commTT 16 a b) &&
    LA.all (fun a => tblEq 16 (compT 16 a a) (idT 16)) &&
    gA.all (memTab 16 LE) && gA.all (memTab 16 bad) &&
    LE.all (fun y => !memTab 16 bad y || memTab 16 LA y) &&
    LS.all (fun y => !LA.all (commIn 16 cT y) || memTab 16 LE y) &&
    LS.all (fun y => !LA.all (commTT 16 y) || memTab 16 LA y)

@[expose] def l7V (nE : Array Table) (gV : Array Table) : Bool :=
  nE.all fun T => !gV.all (commTT 16 T) || tblEq 16 (compT 16 T T) (idT 16)

@[expose] def l7Check (α k : ℕ) : Bool :=
  let nE := nEnum α k
  let good := goodTabs α k
  let bad := badTabs α k
  let LE := (tenum (wgens α k eWords)).toList
  let LS := (tenum (wgens α k sWords)).toList
  let cT := nwT α k cWord
  let eT := nwT α k eWord
  let uT := nwT α k uWord
  l7Fusion nE good eT uT LE && l7Sylow cT eT uT LE LS &&
    l7A bad cT (wgens α k aWords) LE LS && l7V nE (wgens α k vWords) &&
    (badChains α k).all fun c => c.1 == [1, 1]

@[expose] def jTab (α k : ℕ) (W : List Int) : Table := nT α k (jIn α (swN W))

@[expose] def sTab (α k : ℕ) (W : List Int) : Table := nT α k (jOut α (swN W))

@[expose] def chainOK (α k : ℕ) (mT : Table) (W W' : List Int) : Bool :=
  tblEq 16 (conjT 16 (invT 16 mT) (sTab α k W)) (jTab α k W')

@[expose] def hChainWords (k : ℕ) : List Int × List Int :=
  if k = 0 then ([3, 6, 4, 7], [9]) else ([3, 4, 6, 7], [1, 9])

@[expose] def l8Chain (α k : ℕ) (LE : List Table) : Bool :=
  let mT := nwT α k hWord
  let cT := nwT α k cWord
  let y0T := jTab α k [7, 8]
  let Wy := (hChainWords k).1
  let Wv := (hChainWords k).2
  chainOK α k mT [1] [1, 2] && tblEq 16 (sTab α k [1, 2]) cT &&
    chainOK α k mT [7, 8] Wy && !tblEq 16 (sTab α k Wy) y0T &&
      !tblEq 16 (sTab α k Wy) (compT 16 cT y0T) &&
    chainOK α k mT [3] Wv && !memTab 16 LE (sTab α k Wv)

@[expose] def l8Fact (nE : Array Table) (eT : Table) : Bool :=
  let H := nE.toList.filter (commTT 16 eT)
  H.length == 384 &&
    (H.filter fun y => tblEq 16 (compT 16 y (compT 16 y y)) (idT 16) && !tblEq 16 y (idT 16)).all
      fun y => H.any fun z => !memTab 16 [idT 16, y, compT 16 y y] (conjT 16 z y)

@[expose] def l8ZN (nE : Array Table) (cT y0T : Table) (LE : List Table) : Bool :=
  LE.all fun y => !nE.all (commIn 16 cT y) || tblEq 16 y (idT 16) || tblEq 16 y cT ||
    tblEq 16 y y0T || tblEq 16 y (compT 16 y0T cT)

@[expose] def l8Check (α k : ℕ) : Bool :=
  let nE := nEnum α k
  let LE := (tenum (wgens α k eWords)).toList
  l8Fact nE (nwT α k eWord) && l8ZN nE (nwT α k cWord) (jTab α k [7, 8]) LE && l8Chain α k LE

end CFSG.EvenSporadicStandard.M12Std.Yosh
