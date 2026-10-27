module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2MSide
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Case
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsLeaves
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSevenPrime

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem d2ComponentCase_of_cases (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (hS : D2SeitzCross) (hsurv : D2SurvivorsAll) (hM : D2L2MSide) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hU3 : D2CaseU3)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1)
    (hAlt : ∀ (p : ℕ) (hp : 5 ≤ 2 * p), D2IndexCase (.alternating (2 * p) hp))
    (hSpor : D2SporadicCase) : D2ComponentCase :=
  d2ComponentCase_of_families (d2AltCase_of_twoMul hAlt)
    (d2LieCase_of hS (d2IndexCaseAt_lie_char_of hrank kFactLieCharOut kFactLinTwoPrimeRank hL3
      (d2CaseL2Square_of hsurv hM h84 hCGT hD2) hU3) hexc) hSpor

theorem d2ComponentCase_of_current (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6 : D2AltSixCase) (hThree : D2U3Three)
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => IsD2SeitzException p d.1)
    (hSpor : D2SporadicCase) : D2ComponentCase := by
  have hsurv : D2SurvivorsAll :=
    d2SurvivorsAll_of_leaves hrank kFactLinThreeCore hS hexc hSpor
  have hM : D2L2MSide := d2L2MSide_of hα hSch h84 hD2
    (d2BlocksCentralized_of_primeBlocks h84 h85 h86 h93 hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p)
  have hMS : D2U3MSide :=
    d2U3MSide_of unitaryBorelKFacts hα hSch h84 h85 h86 h93 hD2 hK2 hC3 hK5 hKin hKP hC3p hK5p
  exact d2ComponentCase_of_cases hrank kFactLinThreeCore hS hsurv hM h84 hCGT hD2
    (d2CaseU3_of hrank kFactLinThreeCore hS unitaryBorelKFacts hexc hSpor hMS hThree hCGT hD2)
    hexc (d2IndexCase_alt_of (d2AltNoConfig_of_five hAlt5) hA6) hSpor

end CFSG.AGLEmbeddingD2
