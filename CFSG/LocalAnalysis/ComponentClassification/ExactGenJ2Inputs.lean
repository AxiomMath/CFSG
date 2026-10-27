module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenParse
public import Certificates.Data.ExactGen.J2Text
public import Certificates.Data.CFSGNative.PairSchreier.J2Data

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

open CFSG.Sporadic.Schreier.PairNative

@[expose] def j2FC (_ : Unit := ()) : FCCert := parseFC 315 ExactGenData.j2Text

@[expose] def j2FCCheck (_ : Unit := ()) : Bool :=
  let c := j2FC ()
  let S := j2StrongArrs
  c.ok 315 && decide (c.ctx.chP.k = 2) && (c.ctx.chP.S[0]! == S[0]!) &&
    (c.ctx.chP.S[1]! == S[1]!) && decide (c.ctx.chP.order 315 = 604800) &&
    decide (c.ctx.chN.order 315 = 1209600)

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
