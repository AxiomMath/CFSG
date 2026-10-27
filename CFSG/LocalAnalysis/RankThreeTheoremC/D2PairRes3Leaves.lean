module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Leaf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2HSFiveCaseTwo3
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3A6
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2AltFiveBlock3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Families3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Max
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Sz32Five3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

structure D2Leaves3J (G : Type) [Group G] [Finite G] : Prop where
  pairA6 : D2PairA6Residue3 G
  l34Residue : D2L34BetaResidue3 G

structure D2Leaves3FComp (G : Type) [Group G] [Finite G] : Prop where
  pairStrong : D2PairStrongThree3Comp G
  seitzRest : ∀ d : TauCeti.ValidLieTypeIndex,
    D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzLeaf3 p d.1
  hsNonBorel : D2HSFiveNonBorel3 G

theorem D2Leaves3FComp.toLeaves3_of {G : Type} [Group G] [Finite G]
    (hK : D2KFactLeaves) (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hTits5 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusLocalAt (.lie d) fun p => p = 5)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hK4 : KFactSylowThreeAbelian)
    (hHS : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (h : D2Leaves3FComp G) : D2Leaves3 G := by
  have halt : D2AltFive3 G := d2AltFive3_of_blockFacts hK.threeOrFiveDvd hK.catalogSchreier
    hK.eightFour hK.eightFive hK.eightSix hK.nineThree hK.noXBlock3 hK.parabolicThree
    hK.citedBlockThree hK.blockThreeAltSeven hK.blockAltFiveSection hK.blockAltFiveSquare
  have hHS5 : D2IndexCaseAt3 G (.sporadic .HS) fun p => p = 5 :=
    d2IndexCaseAt3_hs_five hK.lieCharRank hK.seitzRankTwo hK.heisMSide3 hK.localCGT hK.noXBlock3
      hHS h.hsNonBorel (fun d hd => d2TorusBorelAt_of_local (hTits5 d hd)) hSzB
      (d2HeisBorelAt_of_local hMcL)
      (d2IndexCaseAt3_sporadic_five_of_rows hK.sporVacuous hK.sections hrows)
  have hSz5 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2IndexCaseAt3 G (.lie d) fun p => p = 5 := fun d hd =>
    d2IndexCaseAt3_sz32_five hK.lieCharRank hK.seitzRankTwo hK.transMSide3 hK.eightFour
      hK.localCGT hK.noXBlock3 hSzB (fun d hd => d2TorusBorelAt_of_local (hTits5 d hd)) hHS
      hMcL.toEq (d2IndexCaseAt3_sporadic_five_of_rows hK.sporVacuous hK.sections hrows) d hd
  refine D2Leaves3.of_families hK
    (d2U3Three3_of_strong hK.eightFour hK.noXBlock3
      (d2U3ThreeStrong3_of_pairStrongComp h.pairStrong))
    halt (d2AltSixCase3_of_strong hK.eightFour hK.noXBlock3
      (d2IndexCaseStrongAt3_of_pairStrongComp (fun _ hp => hp) d2PairAt_altSix d2SolvableAt_altSix
        d2AutomizerAt_altSix d2SylowNineAt_altSix h.pairStrong))
    d2HeisFamily3 (d2HeisFamily3_borel hMcL hK.heisLocalJ4Eleven)
    (fun i p hp => by rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num) d2TorusFamily3
    (d2TorusFamily3_borel hTits5) (fun i p hp => by rcases hp with ⟨_, rfl⟩; norm_num)
    d2VacuousFamily3 (d2VacuousFamily3_vacuous hrows hT3 hK.sporVacuous) ?_ ?_
  · intro d hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK' he
    by_cases hl : IsD2SeitzLTwoEight p d.1
    · exact d2IndexCaseAt3_of_pair (fun _ hp => hp.1) (d2PairAt_l28 d) hK.eightFour hK.noXBlock3
        (d2L28Strong3_of_pairStrongComp hK.catalogSchreier hK4 h.pairStrong d) hS hD1 M hM ha hb p
        hp hl
        P A H R hMP hesc hmax Rbar K hRbar hK' he
    · obtain ⟨hrest, -, hT, hZ⟩ := hpp
      rcases hrest with ⟨rfl, hd | hd | hd⟩ | ⟨rfl, hd | hd⟩
      · exact absurd ⟨rfl, hd⟩ hl
      · exact h.seitzRest d hS hD1 M hM ha hb 3 hp ⟨rfl, hd⟩ P A H R hMP hesc hmax Rbar K hRbar
          hK' he
      · exact absurd (Or.inl ⟨⟨d, rfl, hd⟩, rfl⟩) hZ
      · exact absurd ⟨⟨d, rfl, hd⟩, rfl⟩ hT
      · exact hSz5 d hd hS hD1 M hM ha hb 5 hp rfl P A H R hMP hesc hmax Rbar K hRbar hK' he
  · intro s hs hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK' he
    have h14 : (s, p) ∈ d2SporadicOpenPairs3 := by
      by_contra hout
      exact hpp.2.2 (Or.inr ⟨s, rfl, Or.inr ⟨hs, hout⟩⟩)
    rcases d2SporadicOpenPairs3_cover (s, p) h14 with hrow | hm | hMcL' | hJ4' | hh
    · exact absurd (Or.inr ⟨s, rfl, Or.inl hrow⟩) hpp.2.2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
      exact d2IndexCaseAt3_of_pair (fun _ hp => hp) (d2PairAt_of_maximal hM11) hK.eightFour
        hK.noXBlock3 (d2IndexCaseStrongAt3_of_pairStrongComp (fun _ hp => hp)
          (d2PairAt_of_maximal hM11) (d2SolvableAt_of_maximal hM11) (d2AutomizerAt_m11 hM11 hM11I)
          (d2SylowNineAt_m11 hM11) h.pairStrong) hS hD1 M hM ha hb 3 hp rfl P A H R hMP hesc hmax
        Rbar K hRbar hK' he
    · exact absurd (Or.inl ⟨by rw [(Prod.mk.inj hMcL').1], (Prod.mk.inj hMcL').2⟩) hpp.1
    · exact absurd (Or.inr ⟨by rw [(Prod.mk.inj hJ4').1], (Prod.mk.inj hJ4').2⟩) hpp.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hh
      exact hHS5 hS hD1 M hM ha hb 5 hp rfl P A H R hMP hesc hmax Rbar K hRbar hK' he

theorem D2Leaves3J.toLeaves3FComp {G : Type} [Group G] [Finite G] (hK : D2KFactLeaves)
    (hHS : KFactHSFiveOver) (hF : KFactBlockFiveHeisInner)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hMult : KFactHSMultiplier) (hO3 : KFactBlockThreeOrderThree) (hC5 : KFactBlockRankOneOut)
    (hO : KFactL34Outer) (hI : KFactL34Inner) (hNO : KFactL34NotOrthogonal)
    (hOut : KFactBlockOuterThree) (hK3 : KFactBlockPLElem) (hK4 : KFactSylowThreeAbelian)
    (hE9 : KFactBlockE9Transitive) (h : D2Leaves3J G) : D2Leaves3FComp G :=
  have hpair : D2PairStrongThree3Comp G :=
    d2PairStrongThree3Comp_of_residue hK.eightFour hK.eightFive hK.eightSix hK.nineThree
      hK.noXBlock3 hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven hOut hK3 hE9
      h.pairA6
  ⟨hpair,
    seitzRest_of_residue3_comp hO hI hNO hK.catalogSchreier hK4 hK.eightFour hK.nineThree
      hK.noXBlock3 hpair h.l34Residue,
    d2HSFiveNonBorel3_of_caseTwo hHS hloc hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour
      hK.eightFive hK.eightSix hK.nineThree hK.noXBlock3 hK.parabolicThree hK.citedBlockThree
      hK.blockThreeAltSeven hF
      (d2HSFiveCaseTwo3_of hHS hloc hK.threeOrFiveDvd hK.eightFour hK.eightFive hK.eightSix
        hK.nineThree hK.noXBlock3 hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven hMult
        hO3 hC5)⟩

theorem D2Leaves3J.toLeaves3_of {G : Type} [Group G] [Finite G]
    (hK : D2KFactLeaves) (hHS : KFactHSFiveOver) (hF : KFactBlockFiveHeisInner)
    (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
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
    (hE9 : KFactBlockE9Transitive) (h : D2Leaves3J G) : D2Leaves3 G :=
  (h.toLeaves3FComp hK hHS hF hlocHS hMult hO3 hC5 hO hI hNO hOut hK3 hK4 hE9).toLeaves3_of hK
    hMcL hTits5 hT3 hrows hM11 hM11I hK4 hlocHS hSzB

end CFSG.LocalAnalysis.RankThreeTheoremC
