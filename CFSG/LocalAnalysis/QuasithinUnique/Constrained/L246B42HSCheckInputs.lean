module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr

public section

namespace CFSG.QuasithinUnique.Bridge.HSExcl
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def hsA0A : Array ℕ := hsStrongArrs[0]!

@[expose] def hsA1A : Array ℕ := hsStrongArrs[1]!

@[expose] def hsA0P : PArr := (hsA0A, invCand 3850 hsA0A)

@[expose] def hsA1P : PArr := (hsA1A, invCand 3850 hsA1A)

@[expose] def hsTA (k : ℕ) : Array ℕ := natArr (hsCentTbl k)

@[expose] def hsTP (k : ℕ) : PArr := (hsTA k, hsTA k)

@[expose] def hsSP (k : ℕ) : PArr := (hsTA k, invCand 3850 (hsTA k))

@[expose] def hsSylGens : List PArr := [hsSP 1, hsSP 2, hsSP 3, hsSP 4]

end CFSG.QuasithinUnique.Bridge.HSExcl
