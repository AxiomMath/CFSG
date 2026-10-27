module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Leaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3GroupStep
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3SolvableStrong

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

structure D2Leaves3S (G : Type) [Group G] [Finite G] : Prop where
  pairA6 : D2PairA6Residue3 G
  l34MSolvable : D2L34BetaMSolvableStrong3 G
  l34NonConstrained : D2L34BetaMSideNonConstrainedInput3 G

variable {G : Type} [Group G] [Finite G]

theorem D2Leaves3S.toLeaves3K
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59) (hX : D1NoXBlock3 G) (h : D2Leaves3S G) :
    D2Leaves3K G :=
  ⟨h.pairA6, d2L34BetaMSide3_of_inputs_strong hFF hI59 h.l34MSolvable
    (ffRankTwoInput3_proved hX) (ffNoncyclicInput3_proved hI59 hX) h.l34NonConstrained⟩

theorem D2Leaves3S.toLeaves3_of
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hK : D2KFactLeaves) (hHS : KFactHSFiveOver)
    (hF : KFactBlockFiveHeisInner) (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hTits5 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusLocalAt (.lie d) fun p => p = 5)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr)
    (hlocHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hMult : KFactHSMultiplier) (hO3 : KFactBlockThreeOrderThree) (hC5 : KFactBlockRankOneOut)
    (hO : KFactL34Outer) (hI : KFactL34Inner) (hNO : KFactL34NotOrthogonal)
    (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem) (hK4 : KFactSylowThreeAbelian)
    (hE9 : KFactBlockE9Transitive) (h : D2Leaves3S G) : D2Leaves3 G :=
  (h.toLeaves3K hFF hI59 hK.noXBlock3).toLeaves3_of hK hHS hF hMcL hTits5 hT3 hrows hM11 hM11I
    hlocHS hSzB hMult hO3 hC5 hO hI hNO hOut hK3 hK4 hE9

structure D2Leaves3SW (G : Type) [Group G] [Finite G] : Prop where
  l34MSolvable : D2L34BetaMSolvableStrong3 G
  l34NonConstrained : D2L34BetaMSideNonConstrainedInput3 G

theorem D2Leaves3SW.toLeaves3S (hA6 : D2PairA6Residue3 G) (h : D2Leaves3SW G) : D2Leaves3S G :=
  ⟨hA6, h.l34MSolvable, h.l34NonConstrained⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
