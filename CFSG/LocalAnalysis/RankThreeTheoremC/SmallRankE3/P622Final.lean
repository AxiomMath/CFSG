module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Glue
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Prop65BridgeU0
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614 (KFact64ii)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622KFactD KFactDihedralTypeAut
  KFactReeSylowTwo KFactReeL28 KFactReeBorel KFact2024 KFact2401Three KFact2314 KFact1019
  KFact2025 KFact131 KFactParabolicGen KFact2715 KFactParabolicCover KFactSporThree
  KFact2401Spor KFactSporLocal KFactJ1Sylow KFactJ1L27)

theorem gl83SmallRankProp622_of_kfacts (hK : KFactBlockFactorThreePrime)
    (hL62 : ∀ (G : Type) [Group G] [Finite G], GL83SmallRankLemma62At3 G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hδ : SlotP614CaseDelta) (hcore3 : SlotP614Core) (hnr : SlotP614NormalizerRankLarge)
    (h617 : SlotP614StepL617Large) (hΩ : SlotP614OmegaULarge) (hcoreL : SlotP614CoreLargeU0)
    (hEven3 : KFactFieldAutEvenAt 3) (hOdd3 : KFactFieldAutOddAt 3) (hKD5 : S622KFactD)
    (hK64 : KFact64ii) (h62d : P622CaseDelta4) (h65 : StepP65OddE3U0)
    (hKx3 : P622KxThree) (hL613 : P622L613)
    (hD : KFactDihedralTypeAut)
    (hE : KFactReeSylowTwo) (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025)
    (h131 : KFact131) (hgen : KFactParabolicGen) (h2715 : KFact2715)
    (hcov : KFactParabolicCover) (hS3 : KFactSporThree) (h2401S : KFact2401Spor)
    (hloc : KFactSporLocal) (hJ1 : KFactJ1Sylow) (hJ27 : KFactJ1L27) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G →
      FullCoreLocal G → GL83SmallRankProp622 G :=
  gl83SmallRankProp622_of_open hK hL62 hK1 hK2 hδ hcore3 hnr h617 hΩ hcoreL
      (p622KFactDThree_of_kfacts hEven3 hOdd3) hKD5 hK64 h62d
      (p622Prop65Large_of_stepP65OddE3U0 h65)
      (p622Kx_of_cases hKx3 hL613 hD hE h27 hB h2024 h2401 h2314 h1019 h2025 h131 hgen h2715 hcov
          hS3 h2401S hloc hJ1 hJ27)

theorem gl83SmallRankProp622_of_kfacts3 (hK : KFactBlockFactorThreePrime)
    (hL62 : ∀ (G : Type) [Group G] [Finite G], GL83SmallRankLemma62At3 G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hδ : SlotP614CaseDelta) (hcore3 : SlotP614Core) (hnr : SlotP614NormalizerRankLarge)
    (h617 : SlotP614StepL617Large) (hΩ : SlotP614OmegaULarge) (hcoreL : SlotP614CoreLargeU0)
    (hEven3 : KFactFieldAutEvenAt 3) (hOdd3 : KFactFieldAutOddAt 3) (hKD5 : S622KFactD)
    (hK64 : KFact64ii) (h62d : P622CaseDelta4) (h65 : StepP65OddE3U0)
    (hexit : P622L27Exit) (hKA : KFact2713Three) (hKB : KFactL3U3SL2Three)
    (hKC : KFactParabolicSectionThree) (hKJ : KFactJ1ClosureThree) (hKE : KFactThreeRankTwo)
    (hL613 : P622L613)
    (hD : KFactDihedralTypeAut)
    (hE : KFactReeSylowTwo) (h27 : KFactReeL28) (hB : KFactReeBorel) (h2024 : KFact2024)
    (h2401 : KFact2401Three) (h2314 : KFact2314) (h1019 : KFact1019) (h2025 : KFact2025)
    (h131 : KFact131) (hgen : KFactParabolicGen) (h2715 : KFact2715)
    (hcov : KFactParabolicCover) (hS3 : KFactSporThree) (h2401S : KFact2401Spor)
    (hloc : KFactSporLocal) (hJ1 : KFactJ1Sylow) (hJ27 : KFactJ1L27) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G →
      FullCoreLocal G → GL83SmallRankProp622 G :=
  gl83SmallRankProp622_of_kfacts hK hL62 hK1 hK2 hδ hcore3 hnr h617 hΩ hcoreL hEven3 hOdd3 hKD5
    hK64 h62d h65
    (p622KxThree_of_cases (p622Lemma62Three_of_delta4 hL62 h62d) hexit h131 hgen h2715 h1019 hS3
      hKA hKB hKC hKJ hKE)
    hL613 hD hE h27 hB h2024 h2401 h2314 h1019 h2025 h131 hgen h2715 hcov hS3 h2401S hloc hJ1
    hJ27

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
