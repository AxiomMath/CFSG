module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover

open CFSG.Open TauCeti
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.AGLEmbedding.KFactProofs

theorem kFactAlphaListM3Wide_of_tables (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) :
    KFactAlphaListM3Wide := by
  intro K _ _ hq hcat hZ hZp hZc hrank
  rcases CoverFive.four_le_pRank_three_or_residual hGA hSpor hq hcat hZ hZp hZc with
    h4 | ⟨i, hi, ⟨e⟩⟩
  · omega
  · cases i with
    | cyclic r hr => exact hi.elim
    | alternating n hn =>
      rcases hi with rfl | rfl
      · exact Or.inl ⟨e⟩
      · exact Or.inr (Or.inl ⟨e⟩)
    | sporadic s =>
      rcases hi with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    | lie d =>
      rcases hi with hi | hi
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨d, CoverThree.isLinThreeCover3_of_isLieThreeIndex hi, ⟨e⟩⟩)))
      · exact absurd (CoverThree.coverE6RankFour K hq hZ hZp hZc d hi ⟨e⟩) (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover
