module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenParse
public import Certificates.Data.ExactGen.PSp45Text
public import Certificates.Data.ExactGen.PSp45Gens
public import Certificates.Data.ExactGen.PSp45Rel

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

@[expose] def psp45FC (_ : Unit := ()) : FCCert :=
  let c := parseFC 156 ExactGenData.psp45Text
  { c with
    ctx := { c.ctx with rel := ExactGenData.psp45Rel, relP := ExactGenData.psp45RelP, relK := 30 } }

@[expose] def psp45FCCheck (_ : Unit := ()) : Bool :=
  let c := psp45FC ()
  c.ok 156 && decide (c.ctx.chP.k = 2) && (c.ctx.chP.S[0]! == ExactGenData.psp45G1) &&
    (c.ctx.chP.S[1]! == ExactGenData.psp45G2) && decide (c.ctx.chP.order 156 = 4680000) &&
    decide (c.ctx.chN.order 156 = 9360000)

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
