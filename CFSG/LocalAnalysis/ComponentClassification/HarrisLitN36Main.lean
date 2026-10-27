module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Lie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporAll
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36HS2C
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSporTwoPart
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

theorem statement_holds
    (hHe : TBLit.HeldTrivialMultiplier)
    (hCT : EvenSporadicStandard.CentralTwoBound) (h2B : TwoHSTwoBFact)
    (hON : SolMax.ONOuterComponentsInput) (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hA : EvenLieInvolutionOddCoreFact) (hB : EvenLieOuterCoverFact)
    (hC : PSLTwoOddCharacteristicFact) (hD : L4U4PartialCoverFact)
    (hGA : TBLit.GriessMultipliersAllModels) : Statement :=
  statement_of_rows rowFor_alt (rowFor_classicalRep hGLS hA hB hC hD hGA)
    (rowFor_exceptionalRep hGLS hA hB hC hD hGA)
    (rowFor_sporadicRep hHe (hsj3TwoMultiplierFact_of_centralTwoBound hCT) h2B
      hs2CNormalFact_holds hON)

end CFSG.ComponentClassification.HarrisLit.N36
