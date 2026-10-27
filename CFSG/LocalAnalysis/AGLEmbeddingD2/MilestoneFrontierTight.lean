module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.MilestoneFrontierNodes
public import CFSG.CGT.PushingUpLit.SolKNA.Quaternion
import CFSG.CGT.A8S.Final
import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

theorem lc_gl_embedding_theorem_d2_rank_four_of_frontier_tight
    (hD1 : ∀ (G : Type) [Group G] [Finite G], CFSG.AGLEmbedding.D1Global G → D1For G)
    (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hQL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie)
    (hGLSPlus : Gls3StronglyThreeEmbeddedPlus)
    (h516 : GN.AGL81I516) (hR : GN.GNAltSevenThreeRank)
    (hERest : CFSG.HardMathSupport.Cooperstein.Coordinator.CoopersteinNoFFExceptionalRestNoE8)
    (hnp : CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineNonParabolic)
    (hFO : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNodeFourOrbit)
    (hCF : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNodeColourFour)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hQH : Q ≤ H) : H ≤ M :=
  lc_gl_embedding_theorem_d2_rank_four_of_frontier_nodes hD1 hLowN CFSG.CGT.A8S.a8SylowInput
    (CFSG.CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz hCIT hQL
      CFSG.CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate)
    hGLSPlus h516 hR hERest hnp hFO hCF G hnonab hK hchar he hδ₁ hδ₂ p hp P M hM hPM Q hQ hQrank
    hQM H hH hQH

end CFSG.AGLEmbeddingD2
