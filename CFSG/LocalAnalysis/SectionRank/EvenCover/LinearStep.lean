module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.Assembly.LowTwoRank

theorem even_linear_odd_cover_catalog_step
    {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {n f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n 2 f) : CatalogStepConclusion L := by
  obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect L := hL.1
  obtain ⟨φ, hφ, hker, hD⟩ := even_linear_perfect_odd_cover_map hn hodd e
  exact OddCover.classical_scalar_cover_step Nat.prime_two hf hn (Or.inl ⟨hK, rfl⟩) hSQT hodd φ
    hφ hker hD

end CFSG.SectionRank.EvenCover
