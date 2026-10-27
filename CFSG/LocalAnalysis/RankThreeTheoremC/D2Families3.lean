module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Families3Heis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Families3Torus
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem d2SeitzSpor3_of_cases (HB : TauCeti.CFSGIndex → ℕ → Prop)
    (hHB : ∀ i, D2IndexCaseAt3 G i (HB i))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt3 G (.sporadic s) fun p => ¬ HB (.sporadic s) p) :
    D2SeitzExc3 G ∧ D2SporadicCase3 G := by
  refine ⟨fun d hSet hD1 M hM ha hb p hp hexcp P A H R hMP hesc hmax Rbar K hRbar hK he => ?_,
    fun s hSet hD1 M hM ha hb p hp _ P A H R hMP hesc hmax Rbar K hRbar hK he => ?_⟩
  · by_cases hB : HB (.lie d) p
    · exact hHB (.lie d) hSet hD1 M hM ha hb p hp hB P A H R hMP hesc hmax Rbar K hRbar hK he
    · exact hexc d hSet hD1 M hM ha hb p hp ⟨hexcp, hB⟩ P A H R hMP hesc hmax Rbar K hRbar hK he
  · by_cases hB : HB (.sporadic s) p
    · exact hHB (.sporadic s) hSet hD1 M hM ha hb p hp hB P A H R hMP hesc hmax Rbar K hRbar hK he
    · exact hSpor s hSet hD1 M hM ha hb p hp hB P A H R hMP hesc hmax Rbar K hRbar hK he

theorem d2SeitzSpor3_of_heis (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hCGT : AschbacherLocalCGTBlock) (hX : D1NoXBlock3 G) (hMH : D2HeisMSide3 G)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt3 G (.sporadic s) fun p => ¬ HB (.sporadic s) p) :
    D2SeitzExc3 G ∧ D2SporadicCase3 G :=
  d2SeitzSpor3_of_cases HB (fun i =>
    d2IndexCaseAt3_of_heisBorel hrank hS HB hHB hexc hSpor hMH hCGT hX (hHB i) (hHB5 i)) hexc hSpor

theorem d2SeitzSpor3_of_families (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock) (hX : D1NoXBlock3 G)
    (hMH : D2HeisMSide3 G) (hMT : D2TorusMSide3 G)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p =>
        IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt3 G (.sporadic s) fun p => ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p) :
    D2SeitzExc3 G ∧ D2SporadicCase3 G := by
  have hsurv : D2SurvivorsAll3 G :=
    d2SurvivorsAll3_of_heisTorusLeaves hrank hS HB TB hHB hTB hexc hSpor
  have hTBcase : ∀ i, D2IndexCaseAt3 G i (TB i) := fun i =>
    d2IndexCaseAt3_of_torusBorel (hTB i) (hTB5 i) hMT hsurv h84 hCGT hX
  refine d2SeitzSpor3_of_heis hrank hS hCGT hX hMH HB hHB hHB5 (fun d => ?_) fun s => ?_
  · intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
    by_cases hT : TB (.lie d) p
    · exact hTBcase (.lie d) hSet hD1 M hM ha hb p hp hT P A H R hMP hesc hmax Rbar K hRbar hK he
    · exact hexc d hSet hD1 M hM ha hb p hp ⟨hpp.1, hpp.2, hT⟩ P A H R hMP hesc hmax Rbar K hRbar
        hK he
  · intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
    by_cases hT : TB (.sporadic s) p
    · exact hTBcase (.sporadic s) hSet hD1 M hM ha hb p hp hT P A H R hMP hesc hmax Rbar K hRbar hK
        he
    · exact hSpor s hSet hD1 M hM ha hb p hp ⟨hpp, hT⟩ P A H R hMP hesc hmax Rbar K hRbar hK he

theorem d2SeitzSpor3_of_families_narrow (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (h3 : KFactSeitzRankThreeExceptions) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hX : D1NoXBlock3 G) (hMH : D2HeisMSide3 G)
    (hMT : D2TorusMSide3 G) (hsec : SporSectionFacts3)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (ZK : TauCeti.CFSGIndex → ℕ → Prop) (hZK : ∀ i p, ZK i p → D2VacuousAt i p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p =>
        IsD2SeitzRest p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p ∧ ¬ ZK (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
      D2IndexCaseAt3 G (.sporadic s) fun p =>
        ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p ∧ ¬ ZK (.sporadic s) p) :
    D2SeitzExc3 G ∧ D2SporadicCase3 G := by
  refine d2SeitzSpor3_of_families hrank hS h84 hCGT hX hMH hMT HB hHB hHB5 TB hTB hTB5
    (fun d => ?_) fun s => ?_
  · intro hS' hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
    rcases isD2SeitzException_iff.1 hpp.1 with hr | ⟨hp3, hq⟩
    · by_cases hz : ZK (.lie d) p
      · exact hZK _ p hz _ Rbar _ _ K hK he
      · exact hexc d hS' hD1 M hM ha hb p hp ⟨hr, hpp.2.1, hpp.2.2, hz⟩ P A H R hMP hesc hmax Rbar
          K hRbar hK he
    · subst hp3
      exact hK.false_of_three_le_pRank (h3 K d hq he)
  · by_cases hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)
    · exact d2IndexCaseAt3_of_indexCase3 (d2IndexCase3_sporadic_of_section hsec hs) _
    · refine d2IndexCaseAt3_of_vac_cases
        (Pp := fun p => ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p) (ZK := ZK (.sporadic s))
        (hZK _) ?_
      intro hS' hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
      exact hSpor s hs hS' hD1 M hM ha hb p hp ⟨hpp.1.1, hpp.1.2, hpp.2⟩ P A H R hMP hesc hmax
        Rbar K hRbar hK he

theorem D2KFactLeaves.heisMSide3 (hK : D2KFactLeaves) : D2HeisMSide3 G :=
  d2HeisMSide3_of hK.noXBlock3 hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour hK.eightFive
    hK.eightSix hK.nineThree hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven
    hK.twoGenInner hK.parabolicPrime hK.citedBlockPrime hK.blockAltSevenPrime

theorem D2KFactLeaves.torusMSide3 (hK : D2KFactLeaves) : D2TorusMSide3 G :=
  d2TorusMSide3_of hK.noXBlock3 hK.threeOrFiveDvd hK.catalogSchreier hK.eightFour hK.eightFive
    hK.eightSix hK.nineThree hK.parabolicThree hK.citedBlockThree hK.blockThreeAltSeven
    hK.twoGenInner hK.parabolicPrime hK.citedBlockPrime hK.blockAltSevenPrime

theorem D2Leaves3.of_families (hK : D2KFactLeaves) (hu3 : D2U3Three3 G)
    (halt : D2AltFive3 G) (hsix : D2AltSixCase3 G)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (ZK : TauCeti.CFSGIndex → ℕ → Prop) (hZK : ∀ i p, ZK i p → D2VacuousAt i p)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p =>
        IsD2SeitzRest p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p ∧ ¬ ZK (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
      D2IndexCaseAt3 G (.sporadic s) fun p =>
        ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p ∧ ¬ ZK (.sporadic s) p) :
    D2Leaves3 G :=
  have h := d2SeitzSpor3_of_families_narrow hK.lieCharRank hK.seitzRankTwo hK.seitzRankThree
    hK.eightFour hK.localCGT hK.noXBlock3 hK.heisMSide3 hK.torusMSide3 hK.sections HB hHB hHB5 TB
    hTB hTB5 ZK hZK hexc hSpor
  ⟨d2U3ThreeStrong3_of_u3Three3 hu3,
    d2SeitzExcRestStrong3_of_seitzExcRest3 (d2SeitzExcRest3_of_seitzExc3 h.1), halt,
    d2AltSixStrong3_of_altSixCase3 hsix, d2SporadicOpen3_of_sporadicCase3 h.2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
