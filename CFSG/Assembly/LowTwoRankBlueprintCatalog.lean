module

public import CFSG.Assembly.LowTwoRank
public import CFSG.Blueprint.Catalog
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.Assembly

open LowTwoRank

theorem low_two_rank_blueprint_catalog
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G))
    (hrank : twoRank G ≤ 2) : Blueprint.Catalog G := by
  have h2 : twoRank G = 2 := le_antisymm hrank (two_le_twoRank G hnonab heven)
  rcases rank_two_isomorphism_types G hnonab h2 with
    ⟨p, f, -, -, -, h⟩ | ⟨p, f, -, -, -, h⟩ | ⟨p, f, -, -, -, h⟩ | h | h | h
  · exact .inr (.inr (.inl ⟨.PSL, 2, p, f, h⟩))
  · exact .inr (.inr (.inl ⟨.PSL, 3, p, f, h⟩))
  · exact .inr (.inr (.inl ⟨.PSU, 3, p, f, h⟩))
  · exact .inr (.inr (.inl ⟨.PSU, 3, 2, 2, h⟩))
  · exact .inr (.inl ⟨7, by norm_num, h⟩)
  · obtain ⟨e⟩ := h
    exact .inr (.inr (.inr (.inr ⟨.M11, ⟨e.trans (MulEquiv.subgroupCongr
      CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩⟩)))

end CFSG.Assembly
