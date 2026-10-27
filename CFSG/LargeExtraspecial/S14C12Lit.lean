module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def ReifartSmithU62Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) → ChevalleyExceptionalModel G .twistedE6 2 1

end CFSG.LargeExtraspecial.S14
