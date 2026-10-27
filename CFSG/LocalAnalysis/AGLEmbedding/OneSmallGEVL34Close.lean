module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34MSideBridge
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FF

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1SmallGEVNormalL34Ph7_holds (hFF : CitedFFL34BestOffender)
    (hKZ : KFactMSideAlmostSimpleE27) (hKβ1 : KFactCompFixedThreeEltN)
    (hKZ9 : KFactCompCenterNine) (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree) :
    D1SmallGEVNormalL34Ph7 := by
  intro G _ _ p P M H R Rbar K hd z hz _ hB0 _ _ hp3 hL hOR _ _ hS _ _ hV hCz _ _ _ _ _ _ _
  subst hp3
  exact hd.false_of_hasPrimeConstraint_of_pushUp (d1SmallPushUpL34_of_ff hFF) hβ hα h2 h3 hUE
    hOrb hExp hOut hSh3 hO hNO h93 hD2 hz hB0 rfl hL hOR hV hS
    (L34MSide.hasPrimeConstraint_of_l34 hKZ hKβ1 hKZ9 hUE hOrb hExp hOut hSh3 hO hSch hΓ3 hd hz
      hB0 hL hOR hCz)

theorem d1SmallGEVIbNormalAllRest11_holds (hFF : CitedFFL34BestOffender)
    (hKZ : KFactMSideAlmostSimpleE27) (hKβ1 : KFactCompFixedThreeEltN)
    (hKZ9 : KFactCompCenterNine) (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hUE : KFactUPrimeExc) (hOrb : KFactSmallOrbits)
    (hExp : KFactSmallSylowExp) (hOut : KFactSmallOutPPrime) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree) :
    D1SmallGEVIbNormalAllRest11 := by
  intro G _ _ p P M H R Rbar K hd z hz _ hB0 _ _ hOR _ _ _ _ hV _ _ hp3 hL _ _ hS _ _ _ _ _
  subst hp3
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H :=
    (le_normalizer_glbPrimeCore 3 (Subgroup.centralizer ({z} : Set G))).trans
      ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _).trans hV)
  exact hd.false_of_hasPrimeConstraint_of_pushUp (d1SmallPushUpL34_of_ff hFF) hβ hα h2 h3 hUE
    hOrb hExp hOut hSh3 hO hNO h93 hD2 hz hB0 rfl hL hOR hV hS
    (L34MSide.hasPrimeConstraint_of_l34 hKZ hKβ1 hKZ9 hUE hOrb hExp hOut hSh3 hO hSch hΓ3 hd hz
      hB0 hL hOR hCz)

end CFSG.AGLEmbedding
