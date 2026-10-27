module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Closed
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Endgame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem gl83GenericL28ResiduesE3_holds_of_kfacts (h12 : KFactL28ThreeQuotient)
    (hN : KFactOutThreeNilpotent) (hC : KFactOutThreeCoprime) (hCen : KFactCentralOmega)
    (hM27 : KFactSylowM27) (hGen : KFactFieldGeneration) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeL28Lemma43S G ∧ GL83Generic4_9BNonabS G :=
  gl83P3L28_holds (kFactL28Closed_holds h12 hC hN) (kFactL28Endgame_holds hCen hM27 hGen)

end CFSG.LocalAnalysis.RankThreeTheoremC
