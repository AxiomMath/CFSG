module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S153D31

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15331_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Nonempty (↥(Star153 T I I) ≃* Equiv.Perm (Fin 8))

end CFSG.Quasithin
