module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaMain
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294OD
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29DefChar
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporCo1
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporLy
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporM5
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporHN
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporTable

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

section CertificateInstances


theorem invariantTwoSylowOfD1Rank4_of_cross (hC : KD29Cross)
    (hBT : ∀ q : ℕ, q.Prime → 5 ≤ q →
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQConstrained q) :
    InvariantTwoSylowOfD1Rank4 :=
  invariantTwoSylowOfD1Rank4_of_i294Two
      (gl83I294Two_of kdInndiagP5_holds
          (kd29Inner_of_parts
              (kd29Spor_of_data sporadicOutOdd_holds sporadicRankTable_holds
                  (sporadicClassWitness_of_pairs sporadicClassWitnessAt_Co1_five
                      sporadicClassWitnessAt_HN_five sporadicClassWitnessAt_Ly_five
                      sporadicClassWitnessAt_B_five sporadicClassWitnessAt_M_five
                      sporadicClassWitnessAt_M_seven)) hC (kd29DefChar_of_lieQConstrained hBT))
          i294OutDiagExcluded_holds)

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
