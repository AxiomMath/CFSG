module

public import CFSG.LieType.Multipliers.U43Data
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvData
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

open CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43

@[expose] def letTab (l : Nat) : Array Nat :=
  if l = 0 then tabA else if l = 1 then tabB else if l = 2 then invCand 820 tabA
  else invCand 820 tabB

@[expose] def wordTab (w : List Nat) : Array Nat :=
  w.foldl (fun t l => compA 820 t (letTab l)) (idA 820)

@[expose] def treeTab (root : Array Nat) (step : Array Nat → Nat → Array Nat)
    (par lab : Array Nat) (nl : Nat) : Nat → Nat → Array Nat
  | 0, _ => root
  | f + 1, k => if k = 0 then root else step (treeTab root step par lab nl f par[k]!) (lab[k]! % nl)

@[expose] def fuel : Nat := 32

@[expose] def mulStep (gens : List (Array Nat)) (t : Array Nat) (l : Nat) : Array Nat :=
  if l % 2 = 0 then compA 820 t gens[l / 2]! else compA 820 t (invCand 820 gens[l / 2]!)

@[expose] def conjStep (t : Array Nat) (l : Nat) : Array Nat :=
  compA 820 (compA 820 (letTab l) t) (letTab (l ^^^ 2))

@[expose] def hGens : List (Array Nat) := hGenWords.map wordTab

@[expose] def hTab (k : Nat) : Array Nat := treeTab (idA 820) (mulStep hGens) hPar hLab (2 * hGens.length) fuel k

@[expose] def pGens : List (Array Nat) := pGenIdx.map hTab

@[expose] def pTab (k : Nat) : Array Nat := treeTab (idA 820) (mulStep pGens) pPar pLab (2 * pGens.length) fuel k

@[expose] def cTab (k : Nat) : Array Nat := treeTab tabA conjStep cPar cLab 4 fuel k

@[expose] def fpKey (t : Array Nat) : List Nat := [t[0]!, t[1]!, t[9]!]

@[expose] def distinctOK (T : Nat → Array Nat) (n : Nat) : Bool :=
  decide (((List.range n).map fun k => fpKey (T k)).Nodup)

@[expose] def isInvol (t : Array Nat) : Bool :=
  eqA 820 (compA 820 t t) (idA 820) && !(eqA 820 t (idA 820))

@[expose] def powTab (t : Array Nat) : Nat → Array Nat
  | 0 => idA 820
  | k + 1 => compA 820 t (powTab t k)

@[expose] def closedOK (T : Nat → Array Nat) (tbl : Array Nat) (n nl : Nat)
    (step : Array Nat → Nat → Array Nat) : Bool :=
  (List.range n).all fun k => (List.range nl).all fun l =>
    decide (tbl[k * nl + l]! < n) && eqA 820 (T tbl[k * nl + l]!) (step (T k) l)

@[expose] def conjTab (c b : Array Nat) : Array Nat := compA 820 (compA 820 c b) (invCand 820 c)

@[expose] def f2OK (k : Nat) : Bool :=
  !(isInvol (hTab k) && !(eqA 820 (hTab k) tabA)) ||
    (decide (f2Wit[k]! < 1152) && isInvA 820 (hTab f2Wit[k]!) (invCand 820 (hTab f2Wit[k]!)) &&
      !(eqA 820 (compA 820 (hTab k) (conjTab (hTab f2Wit[k]!) (hTab k)))
        (compA 820 (conjTab (hTab f2Wit[k]!) (hTab k)) (hTab k))))

@[expose] def fuseOK (k : Nat) : Bool :=
  !(isInvol (pTab k)) || (List.range 2835).any fun j => eqA 820 (pTab k) (cTab j)

@[expose] def g0OK : Bool :=
  let g := wordTab g0Word
  let u := compA 820 tabA (conjTab g tabA)
  isInvA 820 g (invCand 820 g) &&
    [1, 2, 3, 4, 5].all fun k => !(eqA 820 (powTab u k) (idA 820))

@[expose] def u43InvCheck (_ : Unit := ()) : Bool :=
  isInvA 820 tabA (invCand 820 tabA) && isInvA 820 tabB (invCand 820 tabB) &&
  (List.range hGens.length).all (fun j =>
    isInvA 820 hGens[j]! (invCand 820 hGens[j]!) &&
    eqA 820 (compA 820 hGens[j]! tabA) (compA 820 tabA hGens[j]!)) &&
  decide (0 < hGens.length) &&
  distinctOK hTab 1152 &&
  closedOK hTab hTbl 1152 (2 * hGens.length) (mulStep hGens) &&
  decide (0 < pGens.length) &&
  (List.range pGens.length).all (fun j => isInvA 820 pGens[j]! (invCand 820 pGens[j]!)) &&
  distinctOK pTab 128 &&
  closedOK pTab pTbl 128 (2 * pGens.length) (mulStep pGens) &&
  distinctOK cTab 2835 &&
  (List.range 128).all fuseOK &&
  (List.range 1152).all f2OK &&
  g0OK

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
