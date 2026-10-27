module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeUnitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeJ4
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent KFactProofs.OrbitsCube

private theorem orbitsCube_of_sylowCube {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    (hrk : Open.pRank p (⊤ : Subgroup K) ≤ 2) (hCube : SylowCube p K) (T : Sylow p K)
    (hw : NormalizerWitness (T : Subgroup K)) :
    (∀ X : Subgroup K, X ≤ T →
      (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ x ∈ X, n * x * n⁻¹ ∈ X) →
      Nat.card X ≠ p ^ 2) ∧
    (∀ t ∈ (T : Subgroup K), t ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * t * n⁻¹ ≠ t) :=
  orbitsCube_of_witness hp (T : Subgroup K) (hCube T).1
    (exists_noncomm_of_cube hp hrk T (hCube T).1 (hCube T).2) hw

private theorem false_of_card_sq_cube {p : ℕ} (hp : p.Prime) {K : Type} [Group K] (T : Sylow p K)
    (h2 : Nat.card T = p ^ 2) (h3 : Nat.card T = p ^ 3) : False := by
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem kFactSmallOrbitsCube_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallOrbitsCube := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hcard
  have hK := isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut
  have hrk := rank_le_two_of_autRank hs hnab hp hAut
  rcases hK with hL | hU | hA | ⟨rfl, hL34 | hM⟩ | ⟨rfl, hTits | hMcL | hFi⟩ | ⟨rfl, hJ⟩
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isSmallLinTwo hp hp2 hL T) hcard).elim
  · exact orbitsCube_of_sylowCube hp hrk (sylowCube_of_isSmallUnitary hp hp2 hU) T
      (normalizerWitness_isSmallUnitary hp hp2 hU T)
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isAltTwoP hp hp2 hA T) hcard).elim
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isLinThreeFour hL34 T) hcard).elim
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isM11 hM T) hcard).elim
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isTitsGroup hTits T) hcard).elim
  · exact orbitsCube_of_sylowCube hp hrk (sylowCube_of_isMcL hs hMcL) T
      (normalizerWitness_isMcL hs hMcL T)
  · exact (false_of_card_sq_cube hp T (sylowSq_of_isFi22 hs hFi T) hcard).elim
  · exact orbitsCube_of_sylowCube hp hrk (sylowCube_of_isJ4 hs hJ) T
      (normalizerWitness_isJ4 hs hJ T)

end CFSG.AGLEmbedding
