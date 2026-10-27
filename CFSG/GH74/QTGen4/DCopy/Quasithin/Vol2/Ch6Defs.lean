module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt6_2_19_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    Nonempty (G ≃* NativeSporadic.M22)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

end CFSG.Quasithin.H13
