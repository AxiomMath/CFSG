module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusJ3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeMathieu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusTh
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeTh
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeHN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi24
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusLy
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLy
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeFi24

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint

@[expose] def SporadicBetaRemainingRest : Prop :=
  SporadicBetaData (NativeSporadic.Carrier .B)

@[expose] def SporadicCaseThreeDataRest : Prop :=
  SporadicCaseThreeData (NativeSporadic.Carrier .B)

section Beta

theorem sporadicBetaRemaining_of_rest (h : SporadicBetaRemainingRest) : SporadicBetaRemaining := by
  intro s hs
  cases s
  all_goals first
    | exact absurd hs (by decide)
    | exact sporadicBetaData_J3
    | exact sporadicBetaData_McL
    | exact sporadicBetaData_Suz
    | exact sporadicBetaData_Co2
    | exact sporadicBetaData_Co3
    | exact sporadicBetaData_Fi22
    | exact sporadicBetaData_Fi23
    | exact sporadicBetaData_HN
    | exact sporadicBetaData_Th
    | exact sporadicBetaData_ONan
    | exact sporadicBetaData_Co1
    | exact sporadicBetaData_Fi24Prime
    | exact sporadicBetaData_Ly
    | exact h

end Beta

section CaseThree

theorem sporadicCaseThreeData_of_rest (h : SporadicCaseThreeDataRest) :
    ∀ s : TauCeti.SporadicName, s ≠ .J3 → s ≠ .M →
      SporadicCaseThreeData (NativeSporadic.Carrier s) := by
  intro s h1 h2
  cases s
  all_goals first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact sporadicCaseThreeData_M11
    | exact sporadicCaseThreeData_M12
    | exact sporadicCaseThreeData_M22
    | exact sporadicCaseThreeData_M23
    | exact sporadicCaseThreeData_M24
    | exact sporadicCaseThreeData_J1
    | exact sporadicCaseThreeData_J2
    | exact sporadicCaseThreeData_J4
    | exact sporadicCaseThreeData_HS
    | exact sporadicCaseThreeData_He
    | exact sporadicCaseThreeData_Ru
    | exact sporadicCaseThreeData_McL
    | exact sporadicCaseThreeData_Co2
    | exact sporadicCaseThreeData_Co3
    | exact sporadicCaseThreeData_Suz
    | exact sporadicCaseThreeData_Fi22
    | exact sporadicCaseThreeData_Co1
    | exact sporadicCaseThreeData_ON
    | exact sporadicCaseThreeData_Th
    | exact sporadicCaseThreeData_HN
    | exact sporadicCaseThreeData_Fi23
    | exact sporadicCaseThreeData_Ly
    | exact sporadicCaseThreeData_Fi24Prime
    | exact h

end CaseThree

end CFSG.AGLEmbedding
