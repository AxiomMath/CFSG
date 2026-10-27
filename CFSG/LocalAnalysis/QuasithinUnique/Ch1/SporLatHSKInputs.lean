module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.HS.Native (hsData)

noncomputable def hsQuotEnumK : Array (List ℕ) × Array ℕ × Array ℕ :=
  bfsEnumB hsData.n hsB (hsQuot1.map (quotGt hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!)))
    (hsQuot1.map (quotGi hsData.n (hsLatK.sTabs ++ hsLatK.mt[1]!))) 1000000

end CFSG.QuasithinUnique.Ch1.SporLat.HS
