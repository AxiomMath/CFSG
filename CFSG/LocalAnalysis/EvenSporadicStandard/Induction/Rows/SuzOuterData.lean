module

public import CFSG.Sporadic.SuzOddCore.InvArrays
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public import CFSG.Sporadic.SuzOddCore.Arrays

public section

namespace CFSG.EvenSporadicStandard.SuzOuter

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore

@[expose] def gensC : Array Tab := invInnerGenArrs 3

@[expose] def letterTab (j : Nat) : Tab :=
  if j < 5 then gensC[j]! else invTab 1782 gensC[j - 5]!

@[expose] def wordTab (gs : Nat → Tab) (w : List Nat) : Tab :=
  w.foldr (fun j acc => comp 1782 (gs j) acc) (idTab 1782)

@[expose] def wordsP : List (List Nat) :=
  [[5, 7, 4, 7, 6, 8, 8, 8, 5, 3, 1, 5, 1, 0, 3, 1, 8],
   [5, 7, 4, 7, 3, 6, 8, 8, 6, 3, 6, 5, 8, 6, 5, 8],
   [3, 4, 5, 8, 8, 6, 8, 8, 5, 8, 5, 8]]

@[expose] def gensP : Array Tab := (wordsP.map (wordTab letterTab)).toArray

@[expose] def repWords : List (List Nat) := [[1, 1], [0], [2]]

@[expose] def repTab (k : Nat) : Tab := wordTab (fun j => gensP[j]!) (repWords.getD k [])

@[expose] def classSizes : List Nat := [315, 2520, 1800]

@[expose] def pairsE : List (Nat × Nat) := [(1, 257), (113, 190), (198, 64), (190, 224)]

@[expose] def gensE (IA : Enum) : Array Tab :=
  (pairsE.map fun p => comp 1782 IA.tabs[p.1]! IA.tabs[p.2]!).toArray

@[expose] def suzOuterCheckWith (gI : Array Tab) (EP IA IB IC EE : Enum) : Bool :=
  gensC.size == 5 && allBelow 5 (fun j => gensC[j]!.size == 1782) &&
    enumOK 1782 gensP EP && EP.tabs.size == 256 &&
    orbitOK 1782 gensC gI (repTab 0) IA && IA.tabs.size == 315 &&
    orbitOK 1782 gensC gI (repTab 1) IB && IB.tabs.size == 2520 &&
    orbitOK 1782 gensC gI (repTab 2) IC && IC.tabs.size == 1800 &&
    coverOK 1782 EP.tabs #[IA.tabs, IB.tabs, IC.tabs] &&
    enumOK 1782 (gensE IA) EE && EE.tabs.size == 128

@[expose] def suzOuterCheck : Bool :=
  let gI := gensC.map (invTab 1782)
  let IA := orbitBFS 1782 gensC gI (repTab 0) 315
  suzOuterCheckWith gI (enumBFS 1782 gensP 256) IA (orbitBFS 1782 gensC gI (repTab 1) 2520)
    (orbitBFS 1782 gensC gI (repTab 2) 1800) (enumBFS 1782 (gensE IA) 128)

end CFSG.EvenSporadicStandard.SuzOuter
