module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Leaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Residue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

structure D2Leaves3K (G : Type) [Group G] [Finite G] : Prop where
  pairA6 : D2PairA6Residue3 G
  l34MSide : D2L34BetaMSide3 G

theorem D2Leaves3K.toLeaves3J
    {G : Type} [Group G] [Finite G] (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hO : KFactL34Outer) (hI : KFactL34Inner)
    (hNO : KFactL34NotOrthogonal) (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem)
    (hK4 : KFactSylowThreeAbelian) (hE9 : KFactBlockE9Transitive) (h : D2Leaves3K G) :
    D2Leaves3J G :=
  have hpair : D2PairStrongThree3Comp G :=
    d2PairStrongThree3Comp_of_residue hK.eightFour hK.eightFive hK.eightSix hK.nineThree
      hK.noXBlock3 hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven hOut hK3 hE9
      h.pairA6
  ⟨h.pairA6, d2L34BetaResidue3_of_mside hK hrows hT3 hM11 hM11I hO hI hNO hK4 hpair h.l34MSide⟩

theorem D2Leaves3K.toLeaves3_of
    {G : Type} [Group G] [Finite G] (hK : D2KFactLeaves) (hHS : KFactHSFiveOver)
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
    (hE9 : KFactBlockE9Transitive) (h : D2Leaves3K G) : D2Leaves3 G :=
  (h.toLeaves3J hK hrows hT3 hM11 hM11I hO hI hNO hOut hK3 hK4 hE9).toLeaves3_of hK hHS hF hMcL
    hTits5 hT3 hrows hM11 hM11I hlocHS hSzB hMult hO3 hC5 hO hI hNO hOut hK3 hK4 hE9

end CFSG.LocalAnalysis.RankThreeTheoremC
