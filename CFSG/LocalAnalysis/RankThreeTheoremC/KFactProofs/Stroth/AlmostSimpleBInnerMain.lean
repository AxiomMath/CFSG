module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthFamily
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerDiagFamily
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerSpFamily
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerSuzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

section Inputs

@[expose] def ChevTwoPClosureOddE6 : Prop := ChevTwoPClosureOddFamily LieFamilyE6

@[expose] def ChevTwoPClosureOddE7 : Prop := ChevTwoPClosureOddFamily LieFamilyE7

@[expose] def ChevTwoPClosureOddE8 : Prop := ChevTwoPClosureOddFamily LieFamilyE8

@[expose] def ChevTwoPClosureOddF4 : Prop := ChevTwoPClosureOddFamily LieFamilyF4

@[expose] def ChevTwoPClosureOddG2 : Prop := ChevTwoPClosureOddFamily LieFamilyG2

@[expose] def ChevTwoPClosureOddTwistedE6 : Prop := ChevTwoPClosureOddFamily LieFamilyTwistedE6

@[expose] def ChevTwoPClosureOddTrialityD4 : Prop := ChevTwoPClosureOddFamily LieFamilyTrialityD4

@[expose] def ChevTwoPClosureOddReeF4 : Prop := ChevTwoPClosureOddFamily LieFamilyReeF4

@[expose] def ChevTwoPClosureOddTits : Prop := ChevTwoPClosureOddFamily LieFamilyTits

end Inputs

theorem chevTwoPClosureOdd_of_inputs
    (hE6 : ChevTwoPClosureOddE6) (hE7 : ChevTwoPClosureOddE7) (hE8 : ChevTwoPClosureOddE8)
    (hF4 : ChevTwoPClosureOddF4) (hG2 : ChevTwoPClosureOddG2)
    (hTwE6 : ChevTwoPClosureOddTwistedE6) (hTri : ChevTwoPClosureOddTrialityD4)
    (hRee : ChevTwoPClosureOddReeF4) (hTits : ChevTwoPClosureOddTits) : ChevTwoPClosureOdd :=
  chevTwoPClosureOdd_of_families chevTwoPClosureOddFamily_linear
    chevTwoPClosureOddFamily_linearDiagThree chevTwoPClosureOddFamily_linearDiagBig
    chevTwoPClosureOddFamily_unitary chevTwoPClosureOddFamily_unitaryDiagThree
    chevTwoPClosureOddFamily_unitaryDiagBig chevTwoPClosureOddFamily_symplectic
    chevTwoPClosureOddFamily_orthogonal hE6 hE7 hE8 hF4 hG2 hTwE6 hTri
    chevTwoPClosureOddFamily_suzuki hRee hTits

theorem chevTwoInnerTwoPartCentralizedRest_of_inputs
    (hE6 : ChevTwoPClosureOddE6) (hE7 : ChevTwoPClosureOddE7) (hE8 : ChevTwoPClosureOddE8)
    (hF4 : ChevTwoPClosureOddF4) (hG2 : ChevTwoPClosureOddG2)
    (hTwE6 : ChevTwoPClosureOddTwistedE6) (hTri : ChevTwoPClosureOddTrialityD4)
    (hRee : ChevTwoPClosureOddReeF4) (hTits : ChevTwoPClosureOddTits) :
    ChevTwoInnerTwoPartCentralizedRest :=
  chevTwoInnerTwoPartCentralizedRest_of_pClosureOdd
    (chevTwoPClosureOdd_of_inputs hE6 hE7 hE8 hF4 hG2 hTwE6 hTri hRee hTits)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
