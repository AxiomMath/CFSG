module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallGEVNormalL34Ph2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    p = 3 → IsLinThreeFour K → ¬ D1SmallOuterR p H Rbar K → D1SmallU2Fails p M H K →
    GLBPrimeCore p (H ⊓ M) ≠ GLBPrimeCore p H → pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    False

theorem d1SmallGEVNormalL34Ph_of_ph2 (hUE : KFactUPrimeExc) (hSch : KFactCatalogSchreier)
    (hΓ3 : KFactSmallGammaSolvableThree) (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hK : CitedBlockToralThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hPh2 : D1SmallGEVNormalL34Ph2) : D1SmallGEVNormalL34Ph := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hcomm hnot hV hCz
    hcore hA
  by_cases hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H
  · have h3 : D1PhaseThree p P M H R :=
      { hd.cfg.ext.toD1Escape with glob := hd.cfg.glob.toAGLGlobal, twoCore_inf := hS }
    exact hd.false_of_l34_ia_of_phaseThree hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86
      h93 hD2 hz hI hB0 hp3 hL hOR h3 hCz
  · exact hPh2 G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL hOR hU2 hne hS hcomm hnot hV
      hCz hcore hA

end CFSG.AGLEmbedding
