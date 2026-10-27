module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG

theorem isComponentOf_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {L K : Subgroup G} (h : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  exact ⟨Subgroup.map_mono hLK, hsub.map e.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm hq⟩

end CFSG
