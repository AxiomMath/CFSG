module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoParts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairPremises

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator CFSG.ProperTwoGeneratedCore.RankOnePair

universe u

theorem rankOnePairFixedDegreeTheorem
    (G : Type u) [Group G] [Finite G] :
    RankOnePairFixedDegreeTheorem G := by
  intro H z h beta hbeta hrank w hwB hw hwz hesc
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, U, hU, -, -, -, -, hmodel, -⟩ :=
    rank_one_pair_centralizer_model_and_two_global_involution_classes h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) beta hbeta hrank hwB hw
      hwz hesc R T₁
  have hUcard : Nat.card U = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
    have hset : (U : Set G) = {1} ∪ distinguishedRoots H z w := by
      rw [hU]
      ext x
      simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [← hset]
    rfl
  rcases hmodel with ⟨hΓ, -⟩ | ⟨hΓ, -⟩ | ⟨hΓ, -⟩
  · exact ⟨1, Or.inl rfl, by rw [hΓ, hUcard, pow_one]⟩
  · exact ⟨2, Or.inr (Or.inl rfl), by rw [hΓ, hUcard]⟩
  · exact ⟨3, Or.inr (Or.inr rfl), by rw [hΓ, hUcard]⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
