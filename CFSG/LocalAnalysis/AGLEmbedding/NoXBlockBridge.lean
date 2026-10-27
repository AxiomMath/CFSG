module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.CGT.PushingUp CFSG.RankThree.PartOne

namespace NoXBlock

variable {G : Type} [Group G] [Finite G]

theorem exists_arrow_maximal {Y : Subgroup G} (hY : InOmega Y) :
    ∃ X : Subgroup G, InOmega X ∧ ∀ Z : Subgroup G, InOmega Z → Arrow X Z → Z = X := by
  obtain ⟨X, hX, hmax⟩ := Set.exists_max_image {X : Subgroup G | InOmega X}
    (fun X => Nat.card X) (Set.toFinite _) ⟨Y, hY⟩
  refine ⟨X, hX, fun Z hZ hXZ => ?_⟩
  rcases hXZ with h | ⟨-, -, -, -, -, -, -, hle, -⟩
  · exact h.symm
  · exact (Subgroup.eq_of_le_of_card_ge hle (hmax Z hZ)).symm

end NoXBlock

end CFSG.AGLEmbedding
