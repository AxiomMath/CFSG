module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLitData

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HSPairs

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
  CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsL1 : List (Array ℕ) := hsSTabs ++ [wordTabA #[hsTa, hsTb] hsData.n hsW1]

@[expose] def hsL2 : List (Array ℕ) := hsSTabs ++ [wordTabA #[hsTa, hsTb] hsData.n hsW2]

end CFSG.QuasithinUnique.Vol2Native.L239.HSPairs
