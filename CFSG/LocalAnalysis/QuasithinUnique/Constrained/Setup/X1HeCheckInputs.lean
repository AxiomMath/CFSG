module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.HeldB.InnerCheckInputs

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

@[expose] def heA0P : PArr := (heGen 0, invCand 8330 (heGen 0))

@[expose] def heA1P : PArr := (heGen 1, invCand 8330 (heGen 1))

@[expose] def heUP : PArr := (heUArr, heUArr)

@[expose] def heT0P : PArr := (heGen 0, heGen 0)

@[expose] def heT1ArrP : PArr := (heT1Arr, heT1Arr)

@[expose] def heSylRegs : List PArr := pRun 8330 [heA0P, heA1P, heUP] heSylProg

@[expose] def heSylGens : List PArr := heSylIdx.map fun k => heSylRegs.getD k (pId 8330)

end CFSG.QuasithinUnique.Setup.X1
