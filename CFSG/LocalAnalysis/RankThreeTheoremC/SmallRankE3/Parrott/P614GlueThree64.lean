module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K64iiDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.SlotFrontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem slotP614Core_of_piecesThree64
    (hB1 : PieceDelta4) (hB2 : PieceNotDeltaThree) (hBδ : PieceDeltaOmega) (hVi : PieceCoreTwo)
    (hE : PieceOmega) (hC : PieceCompSylow) (hD : PieceCompOmegaThree) (hF : PieceChevAlt)
    (hG : Piece619Three) (hH : Piece620Three) (hI : Piece620iii) (hJ : PieceClosing)
    (k64ii : KFact64iiThree) (k64iii : KFact64iii) (kBG : KFactBenderGen) (kTI : KFactBenderTI)
    (k135 : KFact135Three) (kTwo : KFactTwoInvolutionsThree) (kTr : KFactTransvRankOne)
    (k136 : KFact136Three) (k3010 : KFact3010)
    (kKF1 : KFactSylowNormalizerIrreducible) (kKF2 : KFactOutThreePrimeSimple)
    (kZJ : KFactZJFactorizationAny) (kBlk : KFactBlockFactorThreePrime)
    (kCGT : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (kKD : CFSG.LieType.ChevTwo.Chev2KDOut)
    (kCamp : KFactCampbell) (k2813 : KFactLemma2813) (k283 : GL83.I_28_3_S3)
    (kK1 : KFactRankTwoUniqueness) (kK2 : KFactRankThreeStructure)
    (kT29 : KFactProofs.T29.GL83I291Three) (kNC : KFactProofs.T29.NoncyclicCentreRank)
    (kQ : KFactThreeComponentsQRank) :
    SlotP614Core := by
  intro G _ _ hS hD1 P M hsit hαδ x z hx hz H S hopt hcore
  have hU0 : FullCoreLocal G := fullCoreLocal_of_theoremD1_situation_three hS hD1 hsit
  have hyp : Hyp P M x z H S := ⟨hS, hU0, hD1, hsit, hαδ, hx, hz, hopt, hcore⟩
  have hsit' : Sit P M x z := ⟨hS, hU0, hD1, hsit, hx, hz⟩
  have hloc : LocalPair M x z H S :=
    ⟨hopt.ext.pair.isTwoLocal, hopt.ext.pair.le, hopt.ext.pair.not_le, hopt.maxInv,
      hopt.char_le⟩
  have hCT : CoreTwo G := hVi kK1 kK2 kBlk G
  have hOF : OmegaFalse G := hE k64iii G
  have hΩ : OmegaLe x z H := by
    by_cases hα : HasPrimeConstraint (G := M) 3
    · exact hOF P M x z hsit' H S hloc (hCT P M x z hsit' hα H S hloc)
    · exact hBδ k64iii kZJ kBlk kT29 kNC kQ G hOF P M x z H S hyp hα
  have hα : HasPrimeConstraint (G := M) 3 := by
    by_contra hα
    exact hB2 k64ii G P M x z H S hyp hΩ
      (hB1 kT29 kNC kQ G P M x z hS hU0 hD1 hsit hx hz hα)
  have hvi : rankThreePrimeCore 3 H = pCoreOf 2 H := hCT P M x z hsit' hα H S hloc
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, PComp 3 M H K z := by
    by_cases h3 : 3 ∣ (zpowers x ⊔ zpowers z).relIndex H
    · exact hD k64ii G P M x z H S hyp hΩ h3
    · exact hC kKF1 kKF2 G P M x z H S hyp h3
  have h618 : Stage618 M H K z := ⟨hK, hα, hvi, hF kZJ G P M x z H S K hyp hα hvi hK⟩
  have h619 := hG kBG kTI kCGT k135 kKD kTwo kTr G P M x z H S K hyp h618
  obtain ⟨b, h620⟩ := hH k136 kKF2 G P M x z H S K hyp h618 h619
  exact hJ k3010 G P M x z H S K b hyp h618 h620
    (hI kCamp k2813 k283 G hOF hCT P M x z H S K b hyp h618 h619 h620)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
