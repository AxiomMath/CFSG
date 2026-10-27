module

public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public meta import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier

@[expose] def ruFourTest (t : Array ℕ) : Bool :=
  allLt 4060 (fun i => t[t[t[t[i]!]!]!]! == i) && !allLt 4060 (fun i => t[t[i]!]! == i)

@[expose] def tblOfArr (t : Array ℕ) : Table := t.map UInt32.ofNat

@[expose] def letterTab (gens gensInv : Array Table) (z : ℤ) : Table :=
  if 0 < z then gens[z.toNat - 1]! else gensInv[(-z).toNat - 1]!

@[expose] def cGens : Array Table := #[tblOfArr ruC0A, tblOfArr ruC1A]

@[expose] def cGensInv : Array Table := #[tblOfArr (ruInv ruC0A), tblOfArr (ruInv ruC1A)]

@[expose] def lGens : Array Table := ruLGensA.map tblOfArr

@[expose] def lGensInv : Array Table := (ruLGensA.map ruInv).map tblOfArr

@[expose] def fourWordsC : List (List ℤ) :=
  [[1, 2, 2, -1, 2, 2], [1, 1, 2, 2, -1, -1, 2, 2], [1, 1, 1, 1, 1, 2, 2],
   [1, 1, 2, -1, -1, 2, 1, 1, 2, -1, -1, -2], [1, 1, 2, -1, 2, 2, 1, 2, -1, -1, 2, 2],
   [1, 1, 1, 1, 1], [1, 1, 2, -1, 2, -1, -2, 1, -2], [1, 1, 1, 1, 2, -1, 2], [1, 2, 1, -2],
   [1, 1, 1, 2, 1, 2, -1, -1, 2, 2], [1, 1, 1, 2, -1, -1, -1, 2], [1, 1, 2, -1, -1, 2],
   [1, 1, 1, 1, -2, -1, -2], [1, 1, 1, 1, 2, 2, -1, -2, 1, 1, -2], [1, -2, 1, -2], [1, 2],
   [1, 1, 2, 1, -2, -1, 2], [1, 1, 1, 2, -1, -2, -1, 2], [2], [1, 1, 1, 1, 1, 2]]

@[expose] def fourWordsL : List (List ℤ) :=
  [[1, 2, 3], [1, 2, 3, 1, 3, 2, 3, 2], [1, 2, 1, 3, 1, 3, 2, 3], [1, 2, 1, 3, 1, 2, 3, 2],
   [1, 2, 3, 2, 3, 1, 3, 2], [1, 3, 2], [1, 2, 1, 2, 3, 2, 1, 3], [1, 2, 1, 3, 2, 3, 1, 3]]

@[expose] def fourClosuresOK (n : ℕ) (gens gensInv : Array Table) (reps : List Table)
    (cap N : ℕ) : Bool :=
  let cl := reps.map fun r => (r, conjClosure n gens gensInv r cap)
  cl.all (fun c => conjTreeOK n gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 &&
      decide (5 ≤ c.2.1.size)) &&
    keysDistinct n (cl.flatMap fun c => c.2.1.toList) &&
    (cl.map fun c => c.2.1.size).sum == N && reps.all (ordTest n 4)

@[expose] def wordTables (gens gensInv : Array Table) (ws : List (List ℤ)) : List Table :=
  ws.map (wordT 4060 (letterTab gens gensInv))

@[expose] def fourCheckC : Bool :=
  count3 4060 ruLevC ruFourTest == 29136 &&
    fourClosuresOK 4060 cGens cGensInv (wordTables cGens cGensInv fourWordsC) 4000 29136

@[expose] def fourCheckL : Bool :=
  count2 4060 ruLevL ruFourTest == 14560 &&
    fourClosuresOK 4060 lGens lGensInv (wordTables lGens lGensInv fourWordsL) 2000 14560

end CFSG.EvenSporadicStandard.TwoRu.HypOne
