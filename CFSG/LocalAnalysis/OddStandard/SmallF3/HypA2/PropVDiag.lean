module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem centralDatum_of_diagonal (hC : CoverDatum) {K G : Type} [Group K] [Group G] [Finite K]
    [Finite G] (hK : IsQuasisimple K) (hZ : IsPGroup 2 ↥(center K)) (φ : K →* G)
    (hker : φ.ker ≤ center K) (hX : IsFStar ↥φ.range) (hKF : ¬ IsFStar K) : CentralDatum K := by
  have hO : pPrimeCore 2 K = ⊥ := pPrimeCore_eq_bot_of_isQuasisimple hK hZ
  have hZstar : Open.fusionZStar K = center K :=
    fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  have hne : center K ≠ ⊥ := by
    intro hbot
    have hkerbot : φ.ker = ⊥ := by
      rw [hbot] at hker
      exact le_bot_iff.mp hker
    have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hkerbot
    exact hKF ((isFStar_congr (MonoidHom.ofInjective hinj)).mpr hX)
  have hker' : (φ.rangeRestrict).ker ≤ center K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨-, ⟨e⟩⟩ := central_quotient_two_quasisimple φ.rangeRestrict
    φ.rangeRestrict_surjective hker' (isTwoQuasisimple_of_isQuasisimple hK hZ)
  have hFS : FStarSimple (K ⧸ center K) := by
    have h1 : FStarSimple (↥φ.range ⧸ Open.fusionZStar ↥φ.range) := fStarSimple_of_isFStar hX
    have h2 : FStarSimple (K ⧸ Open.fusionZStar K) := (fStarSimple_congr e.symm).mp h1
    exact (fStarSimple_congr (QuotientGroup.quotientMulEquivOfEq hZstar)).mp h2
  exact hC K hK hZ hne hFS hKF

end CFSG.OddStandard.SmallF3.HypA2
