module

public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG.RankThree.PartTwo

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem IsFType.map (φ : G ≃* G') {J : Subgroup G} (h : IsFType J) :
    IsFType (J.map φ.toMonoidHom) := by
  rcases h with ⟨n, hn, h⟩ | h | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | h
  · exact Or.inl ⟨n, hn, h.map φ⟩
  · exact Or.inr (Or.inl (h.map φ))
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm, h.map φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, h.map φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h.map φ))))

theorem IsFType.map_conj {J : Subgroup G} (h : IsFType J) (g : G) :
    IsFType (J.map (MulAut.conj g).toMonoidHom) :=
  h.map (MulAut.conj g)

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

