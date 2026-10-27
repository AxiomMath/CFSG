module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def sgnWord (l : List ℤ) : List (Fin 6 × Bool) :=
  l.map fun a => (Fin.ofNat 6 (a.natAbs - 1), decide (0 < a))

@[expose] def hfxWords : List (List (List ℤ)) :=
  [
    [
      [-1],
      [-2],
      [-3, -4, -3],
      [-4],
      [-4, -5, -4],
      [-6]
    ],
    [
      [2, 3, 2, 6, 3, -1, -6, -2, -3, -1, -2, -1],
      [-6, 1, 2, 3, 2, 1, 4, 6, 1, 1, 4],
      [1, 6, 3, 2, 1, 6, -5, -1, -6, -1, -2, -1, -6, -4, -4, -3, -1, -1, -6, -1, -3, -4, -2, -3,
       -2, -3, -6, -3, -2, 1, 2, 5, 6, 3, 5, 4, 3, -2, -3],
      [1, 6, 3, 2, 1, 6, -5, -1, -6, -1, -2, -1, -6, -4, -4, -3, -1, -1, -6, -1, -3, 2, 3, 2, 4,
       6, 3, 2, 3, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2, 1, 2, 3, 5,
       6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2, -5, -6, -3, -4, -3, -1, -2, -3, -2,
       -5],
      [-3, 2, 3, 2, 3, 1, 2, 6, 1, 3, 6],
      [-3, -6, -3, 1, 6, 3, 2, 3, 4, 6, 3, 1, 2, 1, 3, -2, -5, -4, -3, -6, -5, -4, -2, -1, -6,
       -3]
    ],
    [
      [-2, 1, 5, 4, 6, 1, 2, 5],
      [-5, -6, -4, -5],
      [2, 3, 4, 6, 3, 2, 3, 6, -3, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3,
       -2, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2, -5, -4, -3, -6, -2],
      [-6, -4, -3, -2, -3, -6, -2, 1, 2, 6, 1, 5, 6, 3, 2, -1, -3, -4],
      [-6, -3, 2, 3, 4, 6, 3, 2, 3, 6, -4, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2,
       -5, -3, -2, -6, 1, 6, 3, 2, 5, 4, 6, 3, -2, -1],
      [1, 6, 3, 2, 1, 6, -5, -1, -6, -1, -2, -1, -6, -4, -4, -3, -1, -1, -6, -1, -3, 4, -3, -6,
       -2, -3, -4, -2, -3, -2, 1, 2, 6, 1, 5, 6, 3, 2, -1, -3, -4]
    ],
    [
      [-3, 2, 3, 6, 1, 2, 5, 6, 1, 5, 6, 3, -2, -3],
      [1, 6, 3, 2, 1, 6, -5, -1, -6, -1, -2, -1, -6, -4, -4, -3, -1, -1, -6, -1, -3, 2, 3, 4, 3,
       2, 6, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2, 1, 2, 5, 6, 3, 4,
       5, 3],
      [-6, 2, 3, 2, 6, 5, 6, 3, 2, 1, 3, 6, -5],
      [-6, -3, 1, 6, 3, 2, 1, 6, -5, -1, -6, -1, -2, -1, -6, -4, -4, -3, -1, -1, -6, -1, -3, 2,
       3, 2, 6, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2, -2, 1, 2, 5, 6,
       1, 5, 6, 3, -2, -3],
      [4, 3, 6, -5, -6, -3, -4],
      [-6, 2, 3, 4, 3, 2, 3, 1, 2, 3, 5, 6, 3, -4, -5, -5, -2, -3, -2, -6, -3, -2, -5, -3, -2,
       -4, 1, 5, 4, 3, 6, 5, 4, 3, -2, -3, -2]
    ]
  ]

@[expose] def hfxElemWords : List (List (List ℤ)) :=
  [
    [
      [-3, -4, -2, -3, -5, -2, -3, -2, -4, -3, -6, -5, -1, -6, -4, -2, -1, -5, -6],
      [-3, -4, -2, -3, -2, -3, -2, -6, -3, -2, -3, -4, -2, -3, -6],
      [-4, -2, -6],
      [-3, 2, 4, 3, 2, 5, 3, 2, -1, -4, -3, -6, -5, -1, -6, -4, -2, -1, -5, -6]
    ],
    [
      [-5, -3, -4, -5, -3, -2, -6, -3, -4, -5, -4, -3, -2, -6, -3, -5, -4, -3, -5],
      [-3, -6, -3, -5, -2, -1, -6, -1, -2, -5, -3, -6],
      [-6, -5, -3, -2, -3, -1, -6],
      [-2, -3, -4, -2, -3, -1, -2, -3, -5, -4, -3, -2, -1, -6, -5, -1, -6, -2, -3, -2, -3, -2,
       -4]
    ],
    [
      [-5, -1, -3, -2, -3, -2, -3, -4, -3, -1, -2, -5, -4, -6, -5, -3, -4, -2],
      [-3, -2, -3, -4, -3, -1, -2, -6, -5, -1, -6, -4, -2, -1, -3, -2, -4, -3],
      [-3, 2, 3, 2, 3, 4, 5, 4, -6, -5, -4, -3, -2, -3, -2],
      [2, 3, 2, 3, 4, 5, -6, -5, -4, -3, -2, -3, -2]
    ],
    [
      [-4, -6, -5, -3, -6, -4, -3, -5, -4, -6],
      [-5, -1, -3, 2, 3, 2, 4, 3, -6, -3, -5, -6, -4, -2, -1, -5, -6, -3],
      [-1, -3, -4, -5, -2, -3, -2, -3, -2, -4, -3, -6, -5, -4, -3, -2, -3, -6, -3, -2, -1],
      [-2, -3, -2, -1, -6, -3, -5, -2, -3, -6, -1, -2, -3, -2]
    ]
  ]

@[expose] def hfxW (i : Fin 4) (j : Fin 6) : List (Fin 6 × Bool) :=
  sgnWord ((hfxWords.getD i.val []).getD j.val [])

@[expose] def hfxE (i l : Fin 4) : List (Fin 6 × Bool) :=
  sgnWord ((hfxElemWords.getD i.val []).getD l.val [])

@[expose] def hfxRho (i : Fin 4) : Table := hsCentTbl ([5, 12, 21, 34].getD i.val 0)

@[expose] def hfxT (i : Fin 4) (j : Fin 6) : Table := evalW 11200 harY harYI (hfxW i j)

@[expose] def hfxTI (i : Fin 4) (j : Fin 6) : Table := invT 11200 (hfxT i j)

@[expose] def hfxA (i : Fin 4) (k : Fin 6) : Table :=
  evalW 11200 (hfxT i) (hfxTI i) (hsCommWord k)

@[expose] def hfxAI (i : Fin 4) (k : Fin 6) : Table := invT 11200 (hfxA i k)

@[expose] def hfxEt (i l : Fin 4) : Table := evalW 11200 harY harYI (hfxE i l)

@[expose] def hfxEa (i l : Fin 4) : Table := evalW 11200 (hfxA i) (hfxAI i) (hfxE i l)

@[expose] def hfxProd (Et : Fin 4 → Table) (m : ℕ) : Table :=
  (List.finRange 4).foldl
    (fun acc l => if m.testBit l.val then compT 11200 acc (Et l) else acc) (idT 11200)

@[expose] def hfxCheckWith (i : Fin 4) (T TI A AI : Fin 6 → Table) (Et Ea : Fin 4 → Table)
    (P : Fin 16 → Table) : Bool :=
  permOK 3850 (hfxRho i) && invOK 3850 (hfxRho i) (invT 3850 (hfxRho i)) &&
  (List.finRange 6).all (fun j => tblEq 3850 (evalW 3850 harX harXI (hfxW i j))
    (compT 3850 (compT 3850 (hfxRho i) (harX j)) (invT 3850 (hfxRho i)))) &&
  (List.finRange 6).all (fun j => invOK 11200 (T j) (TI j)) &&
  (List.finRange 6).all (fun k => invOK 11200 (A k) (AI k)) &&
  (List.finRange 4).all (fun l => tblEq 11200 (Et l) (Ea l)) &&
  (List.finRange 4).all (fun l => tblEq 11200 (compT 11200 (Et l) (Et l)) (idT 11200)) &&
  (List.finRange 4).all (fun l => (List.finRange 4).all fun l' =>
    tblEq 11200 (compT 11200 (Et l) (Et l')) (compT 11200 (Et l') (Et l))) &&
  (List.finRange 16).all (fun a => (List.finRange 16).all fun b =>
    a == b || !tblEq 11200 (P a) (P b))

@[expose] def hfxCheck (i : Fin 4) : Bool :=
  let Ts : Array Table := Array.ofFn (hfxT i)
  let TIs : Array Table := Array.ofFn fun j : Fin 6 => invT 11200 Ts[j.val]!
  let As : Array Table := Array.ofFn fun k : Fin 6 =>
    evalW 11200 (fun j => Ts[j.val]!) (fun j => TIs[j.val]!) (hsCommWord k)
  let AIs : Array Table := Array.ofFn fun k : Fin 6 => invT 11200 As[k.val]!
  let Ets : Array Table := Array.ofFn (hfxEt i)
  let Eas : Array Table := Array.ofFn fun l : Fin 4 =>
    evalW 11200 (fun k => As[k.val]!) (fun k => AIs[k.val]!) (hfxE i l)
  let Ps : Array Table := Array.ofFn fun m : Fin 16 => hfxProd (fun l => Ets[l.val]!) m.val
  hfxCheckWith i (fun j => Ts[j.val]!) (fun j => TIs[j.val]!) (fun k => As[k.val]!)
    (fun k => AIs[k.val]!) (fun l => Ets[l.val]!) (fun l => Eas[l.val]!) (fun m => Ps[m.val]!)

@[expose] def hfxOK : Bool := (List.finRange 4).all hfxCheck

end CFSG.EvenSporadicStandard.TwoHS
