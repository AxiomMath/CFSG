module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Sporadic.Schreier.RuArrays

public section

namespace CFSG.QuasithinUnique.Bridge.RuExcl
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native

@[expose] def ruA0P : PArr := (ruA0A, ruInv ruA0A)

@[expose] def ruA1P : PArr := (ruA1A, ruInv ruA1A)

@[expose] def ruZtArr : Array ℕ := compA 4060 ruA1A ruA1A

@[expose] def ruZtP : PArr := (ruZtArr, ruZtArr)

end CFSG.QuasithinUnique.Bridge.RuExcl
