module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.ClassicalInvolution.NormalQuaternion
import CFSG.Adapters.TauCetiExceptional.ReeCatalog
import CFSG.Assembly.ComponentType
import CFSG.RankThree.GF2n.Item310

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup CFSG.Open

theorem oddLieType_or_mathieu_of_normalQuaternionAt (hCIT : ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) (hQ : CFSG.ClassicalInvolution.NormalQuaternionAt z) :
    Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      Blueprint.NativeSporadic.IsSporadic G .M12 := by
  obtain ⟨K, hKC, hKn, hzK, P, r, hr, hP⟩ := hQ
  have hsub : CFSG.Open.IsSubnormal K (centralizer ({z} : Set G)) :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hKC hKn
  have hTE : classicalInvolutionTightlyEmbedded K :=
    (CFSG.ClassicalInvolution.tightlyEmbedded_iff_centralizer_le_normalizer hzK hz hKC P
      ⟨r, hr, hP⟩).2
      ((normal_subgroupOf_iff_le_normalizer hKC).1 hKn)
  let eF : genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases (hCIT G hFnonab z hz K hzK hsub P ⟨r, hr, hP⟩).2 hTE with h | h | h
  · exact .inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr (.inl ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))
  · exact .inr (.inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))

theorem inCatalog_of_normalQuaternionAt
    (hCIT : ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) (hQ : CFSG.ClassicalInvolution.NormalQuaternionAt z) :
    CFSG.Assembly.InCatalog G := by
  rcases oddLieType_or_mathieu_of_normalQuaternionAt hCIT hnonab hz hQ with h | h | h
  · exact CFSG.Assembly.ComponentType.oddLieType_inCatalog G
      (CFSG.TauCetiBridge.componentType_oddLieType_of_blueprint_of_odd G h)
  · exact CFSG.RankThree.GF2n.sporadicBridge_M11 G h
  · exact CFSG.RankThree.GF2n.sporadicBridge_M12 G h

end CFSG.ComponentClassification.StandardRecognition
