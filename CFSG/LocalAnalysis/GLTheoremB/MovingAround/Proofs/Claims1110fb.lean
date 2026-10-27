module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110f
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreMain
public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemma1110CaseB_of_pieces'_cert
    (h119 : Lemma119Statement) (h111 : Prop111Statement)
    (h112 : CFSG.HardMathSupport.Solomon.LocalBalance.Input11_2) (h183 : Prop115.Input18_3Gen)
    (hSeitz : Claims1116.Input23_10) (hSchur : Lemma123.InputSchurAlt')
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hO : Claims1314.Exc5Orders) (hLn : InputA5UpLn)
    (hO5 : InputOut5Lie) (h305 : Input30_5) (hSyl : InputU5Sylow) (hD4 : InputGammaD4)
    (h6 : Step6K1Claim) : Lemma1110CaseB :=
  lemma1110CaseB_of_pieces' h119 h111 h112 h183 hSeitz CFSG.HardMathSupport.Solomon.Proving.fi22Facts_holds
    Claims1110b.inputFi22OneClassFive_holds CFSG.AGLEmbedding.kFactUPrimeExcFi22 hSchur hSpM hOut hGA hO hLn hO5
    h305 hSyl hD4 h6

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110f
