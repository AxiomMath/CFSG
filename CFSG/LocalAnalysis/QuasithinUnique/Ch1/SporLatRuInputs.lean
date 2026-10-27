module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert

@[expose] def ruQuot1 : List QuotGen := [
  ⟨[3, 3, 2, 2, 0, 3, 0, 1, 2, 3, 1, 2, 2, 0, 2, 1, 3], 8, 3⟩,
  ⟨[1, 3, 0, 1, 1, 0, 1, 3, 1, 3, 1, 2, 3, 0, 0, 2, 2, 0, 0, 2, 1, 3, 2, 0, 1, 2], 4, 3⟩]

@[expose] def ruQuotL1 : List (Array ℕ) :=
  ruSTabsL ++ (ruMw[1]!).map (wordTabA #[ruTaL, ruTbL] ruData.n)

@[expose] def ruQuotEnum : Array (List ℕ) × Array ℕ × Array ℕ :=
  bfsEnumB ruData.n ruB (ruQuot1.map (quotGt ruData.n ruQuotL1))
    (ruQuot1.map (quotGi ruData.n ruQuotL1)) 1000000

end CFSG.QuasithinUnique.Ch1.SporLat.Ru
