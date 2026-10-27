module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def g4iT : Tab := invTab 42 g₄T

@[expose] def g44T : Tab := comp 42 g₄T g₄T

@[expose] def g44iT : Tab := comp 42 g4iT g4iT

@[expose] def repT : Array Tab :=
  #[r₁T, g₅T, conjTab 42 g₄T g4iT g₅T, conjTab 42 g44T g44iT g₅T, g₆T, conjTab 42 g₄T g4iT g₆T,
    conjTab 42 g44T g44iT g₆T, r₄T]

@[expose] def gensSInv : Array Tab := gensS.map (invTab 42)

@[expose] def orbS (x : Tab) : Enum := orbitBFS 42 gensS gensSInv x 400

@[expose, noinline] def cosetCheck (ES ER : Array Tab) : Bool :=
  (allBelow 8 fun i => orbitOK 42 gensS gensSInv repT[i]! (orbS repT[i]!)) &&
    coverOK 42 ER (repT.map fun x => (orbS x).tabs) &&
    (allBelow 8 fun i => allBelow 8 fun j => i == j ||
      notInOK ES (comp 42 (invTab 42 repT[i]!) repT[j]!)) &&
    (allBelow 8 fun i => (invTab 42 repT[i]!).size == 42 &&
      comp 42 (invTab 42 repT[i]!) repT[i]! == idTab 42) &&
    g4iT.size == 42 && comp 42 g4iT g₄T == idTab 42

end CFSG.ComponentClassification.CatFactsL4U4
