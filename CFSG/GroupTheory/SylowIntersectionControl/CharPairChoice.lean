module

public import CFSG.GroupTheory.SylowIntersectionControl.CharPair
public import CFSG.GroupTheory.SylowIntersectionControl.PairSelection
import CFSG.GroupTheory.SylowIntersectionControl.CharPairExists

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

theorem exists_gnPairChoice_isGomiCharPairGN {G : Type} [Group G] [Finite G] :
    ∃ c : GNPairChoice G, ∀ T : Subgroup G, IsPGroup 2 T → baum T = T → T ≠ ⊥ →
      IsGomiCharPairGN T (c.fst T) (c.snd T) :=
  GNPairChoice.exists_forall _ (fun _ _ _ h g => h.map_mulEquiv (MulAut.conj g))
    fun T hT hK hne => by
      obtain ⟨T₁, T₂, h⟩ := exists_isGomiCharPairGN T hT hne hK
      exact ⟨T₁, T₂, h.2.1, h.2.2.2, h.1.2.1, h.2.2.1, h.1.2.2.1, h.1.2.2.2.1, h⟩

end CFSG.GroupTheory

end
