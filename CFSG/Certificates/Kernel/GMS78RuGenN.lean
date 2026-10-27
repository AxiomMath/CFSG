module

public import CFSG.Certificates.Kernel.GMS78RuGen

public section

namespace CFSG.KC.GMS.Gen

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuS CFSG.GMS78RuN

section NModel

variable (nbt ntw : List (List (Fin 8))) (nc nb : List Nat)

@[expose] def nCoArr : Array Nat := Array.ofFn (n := 256) fun m => nCo nc m.val

@[expose] def nRowArr : Array (Fin 8) :=
  Array.ofFn (n := 2048) fun k => xs8 (nCoArr nc)[k.val % 256]! (nBT nbt (k.val / 256))

@[expose] def nBetaF (m n : Nat) : Fin 8 := xs8 (nCoArr nc)[m]! fun j => (nRowArr nbt nc)[256 * j + n]!

@[expose] def nBetaArr : Array (Fin 8) :=
  Array.ofFn (n := 65536) fun i => nBetaF nbt nc (i.val / 256) (i.val % 256)

@[expose] def nGamBArr (r : Lin8) (ad : Array Nat) : Array (Fin 8) :=
  Array.ofFn (n := 64) fun k =>
    (nBetaArr nbt nc)[ad[nB nb (k.val / 8)]! * 256 + ad[nB nb (k.val % 8)]!]! ^^^
      linApply r (nBetaArr nbt nc)[nB nb (k.val / 8) * 256 + nB nb (k.val % 8)]!

@[expose] def nTauArrW (r : Lin8) (g : Array (Fin 8)) : Array (Fin 8) :=
  Array.ofFn (n := 256) fun m =>
    xs8 (nCoArr nc)[m.val]! (nTw ntw r) ^^^
      xs8 (nCoArr nc)[m.val]! fun j => xs8 (nCoArr nc)[m.val]! fun i => if i < j then g[8 * i + j]! else 0

@[expose] def nTauTab : Array (Array (Fin 8)) :=
  Array.ofFn (n := 512) fun k =>
    let r := nCode k.val
    if indep3 r.1 r.2.1 r.2.2 then nTauArrW ntw nc r (nGamBArr nbt nc nb r nAdTab[k.val]!) else #[]

@[expose] def nQuadCheck : Bool :=
  glList.all fun r =>
    let ad := nAdTab[nIdx r]!
    let tau := (nTauTab nbt ntw nc nb)[nIdx r]!
    (List.range 256).all fun m => (List.range 8).all fun j =>
      let b := nB nb j
      tau[m ^^^ b]! == tau[m]! ^^^ tau[b]! ^^^
        ((nBetaArr nbt nc)[ad[m]! * 256 + ad[b]!]! ^^^ linApply r (nBetaArr nbt nc)[m * 256 + b]!)

@[expose] def nCompCheck : Bool :=
  glList.all fun r => glList.all fun s =>
    let rs := linComp r s
    let adr := nAdTab[nIdx r]!
    let ads := nAdTab[nIdx s]!
    let adrs := nAdTab[nIdx rs]!
    let taur := (nTauTab nbt ntw nc nb)[nIdx r]!
    let taus := (nTauTab nbt ntw nc nb)[nIdx s]!
    let taurs := (nTauTab nbt ntw nc nb)[nIdx rs]!
    (List.range 8).all fun k =>
      adrs[2 ^ k]! == adr[ads[2 ^ k]!]! &&
        taurs[nB nb k]! == taur[ads[nB nb k]!]! ^^^ linApply r taus[nB nb k]!

@[expose] def nIdCheck : Bool :=
  (List.range 256).all (fun m => (nAdTab[nIdx linId]!)[m]! == m &&
    ((nTauTab nbt ntw nc nb)[nIdx linId]!)[m]! == 0 && maskApply nb (nCoArr nc)[m]! == m) &&
    glList.all (fun r => glList.contains (linInv r) && linComp (linInv r) r == linId &&
      linComp r (linInv r) == linId) &&
    glList.all (fun r => glList.all fun s => glList.contains (linComp r s))

@[expose] def nFaithCheck : Bool :=
  ((List.range 255).all fun m => (List.range 256).any fun n =>
    (nBetaArr nbt nc)[(m + 1) * 256 + n]! != (nBetaArr nbt nc)[n * 256 + (m + 1)]!) &&
    ((List.finRange 8).all fun t => (List.finRange 8).all fun t' =>
      t == 0 || t' == 0 || glList.any fun s => linApply s t == t')

@[expose] def nMulT (p q : NTrip) : NTrip :=
  let am := (nAdTab[nIdx p.2.2]!)[q.1]!
  (p.1 ^^^ am, p.2.1 ^^^ (linApply p.2.2 q.2.1 ^^^ ((nTauTab nbt ntw nc nb)[nIdx p.2.2]!)[q.1]!) ^^^
    (nBetaArr nbt nc)[p.1 * 256 + am]!, linComp p.2.2 q.2.2)

variable (img imgInv : List NTrip)

@[expose] def nSign (p : Fin 7 × Bool) : NTrip :=
  if p.2 then img.getD p.1 nOneT else imgInv.getD p.1 nOneT

@[expose] def nEvalW (w : List (Fin 7 × Bool)) : NTrip :=
  w.foldl (fun x p => nMulT nbt ntw nc nb x (nSign img imgInv p)) nOneT

@[expose] def nImgCheck : Bool :=
  (List.range 7).all fun i => nValid (img.getD i nOneT) && nValid (imgInv.getD i nOneT) &&
    nMulT nbt ntw nc nb (img.getD i nOneT) (imgInv.getD i nOneT) == nOneT

@[expose] def nRelCheck (rels : List (List Nat)) : Bool :=
  rels.all fun r => nEvalW nbt ntw nc nb img imgInv (CFSG.CosetTable.wordOfCodes 7 r) == nOneT

@[expose] def nCloCheck (rW kW : List (List Nat)) (rT : List NTrip) : Bool :=
  ((List.range 11).all fun i =>
    nEvalW nbt ntw nc nb img imgInv (CFSG.CosetTable.wordOfCodes 7 (rW.getD i [])) == rT.getD i nOneT) &&
    ((List.range 168).all fun i =>
      nEvalW nbt ntw nc nb img imgInv (CFSG.CosetTable.wordOfCodes 7 (kW.getD i [])) ==
        (0, 0, glList.getD i linId))

@[expose] def nA0Check (a0 : List (List (Fin 7 × Bool))) : Bool :=
  a0.all fun w => (nEvalW nbt ntw nc nb img imgInv w).1 == 0 &&
    (nEvalW nbt ntw nc nb img imgInv w).2.2 == linId

end NModel

end CFSG.KC.GMS.Gen

end
