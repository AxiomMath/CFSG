module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique

theorem IsSylowTwoOf.map_mulEquiv {Y Z : Type} [Group Y] [Group Z] [Finite Y] [Finite Z]
    {S H : Subgroup Y} (f : Y ≃* Z) (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map f.toMonoidHom) (H.map f.toMonoidHom) := by
  rw [isSylowTwoOf_iff] at h ⊢
  obtain ⟨hle, hS, hc⟩ := h
  refine ⟨Subgroup.map_mono hle, hS.map f.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective f.injective, hc]
  show twoPart H = twoPart (H.map f.toMonoidHom)
  unfold twoPart
  rw [Subgroup.card_map_of_injective f.injective]

end CFSG.QuasithinUnique

end
