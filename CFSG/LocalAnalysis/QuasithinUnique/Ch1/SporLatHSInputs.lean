module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Open (pCoreOf)

@[expose] def hsDelta : List ℕ := [213, 278, 582, 618, 782, 798, 950, 1057]

@[expose] def hsSTabs : List (Array ℕ) := hsQp.map fun p => hsSLP[p.1]!

@[expose] def hsLat : LatData (List ℕ) := buildLat ptAct hsData.n hsTa hsTb hsDelta hsSTabs 400

@[expose] def hsOt : Array (OmegaData (List (List ℕ))) := buildO2 ptAct hsLat

@[expose] def hsQuot1 : List QuotGen := [
  ⟨[2, 2, 2, 0, 3, 1, 1, 2, 0, 0, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3, 3, 3, 1, 0, 2, 3, 2, 0, 2, 3, 3, 0,
    0, 1, 3, 2, 3, 0, 0, 3, 1, 0, 0, 3, 3, 1, 2, 3, 2, 0, 3, 0, 3, 3, 3, 2, 2, 3, 2, 2], 4, 3⟩,
  ⟨[2, 3, 0, 1, 3, 0, 2, 2, 2, 2, 2, 1, 1, 1, 3, 0, 2, 0, 1, 1, 3, 0, 3, 0, 2, 2, 1, 0, 3, 3, 1, 1,
    3, 1, 2, 1, 0, 0, 2, 1, 2, 0, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 2, 3, 3, 3, 0, 0, 2], 2, 5⟩]

@[expose] def hsQuotEnum : Array (List ℕ) × Array ℕ × Array ℕ :=
  bfsEnumB hsData.n hsB (hsQuot1.map (quotGt hsData.n (hsLat.sTabs ++ hsLat.mt[1]!)))
    (hsQuot1.map (quotGi hsData.n (hsLat.sTabs ++ hsLat.mt[1]!))) 1000000

end CFSG.QuasithinUnique.Ch1.SporLat.HS
