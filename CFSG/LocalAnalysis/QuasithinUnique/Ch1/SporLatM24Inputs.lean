module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.Open (pCoreOf)

@[expose] def m24Sets : List (List ℕ) :=
  [[0, 2, 3, 7], [1, 6, 8, 9], [4, 5, 12, 18], [10, 15, 17, 21], [11, 14, 16, 20],
    [13, 19, 22, 23], [1, 9], [4, 12], [5, 18], [6, 8]]

@[expose] def m24Delta : List ℕ := sortN (m24Sets.map (encodeSet 24))

@[expose] def m24STabs : List (Array ℕ) := m24Qp.map fun p => m24SLP[p.1]!

@[expose] def m24Lat : LatData (List ℕ) :=
  buildLat (codeSetAct 24) 24 m24ta.toArray m24tb.toArray m24Delta m24STabs 400

@[expose] def m24Ot : Array (OmegaData (List (List ℕ))) := buildO2 (codeSetAct 24) m24Lat

@[expose] def m24Mems : List Mem :=
  [⟨1024, 1024, 1024⟩, ⟨322560, 16, 322560⟩, ⟨64512, 64, 64512⟩, ⟨138240, 64, 138240⟩,
    ⟨21504, 128, 21504⟩, ⟨9216, 256, 9216⟩, ⟨21504, 128, 21504⟩, ⟨3072, 512, 3072⟩,
    ⟨3072, 512, 3072⟩, ⟨3072, 512, 3072⟩, ⟨9216, 256, 9216⟩, ⟨3072, 512, 3072⟩,
    ⟨9216, 256, 9216⟩]

end CFSG.QuasithinUnique.Ch1.SporLat.M24
