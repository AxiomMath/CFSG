module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE7Final
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Holds
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Final3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances


theorem kd29Inner_holds : KD29Inner :=
  kd29Inner_of_parts
    (kd29Spor_of_data sporadicOutOdd_holds sporadicRankTable_holds
      (sporadicClassWitness_of_pairs sporadicClassWitnessAt_Co1_five sporadicClassWitnessAt_HN_five
        sporadicClassWitnessAt_Ly_five sporadicClassWitnessAt_B_five sporadicClassWitnessAt_M_five
        sporadicClassWitnessAt_M_seven))
    (kd29Cross_of_e7_e8
      (crossE7SevenSplit_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE7SevenSplit_holds)
      (crossE8FiveFour_of_rank
        RankThreeTheoremC.KFactProofs.Stroth.Bal3.i294CrossLargePrime_holds
        crossRankE8FiveFour_holds))
    (kd29DefChar_of_lieQConstrained fun _ hq hq5 =>
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrained_odd hq (by omega))

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
