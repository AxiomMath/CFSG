module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadDouble

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs

variable {G : Type} [Group G]

@[expose] def PspNoA2At (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) : Prop :=
  ∀ L ∈ Ω, ∀ l : G, IsUniqueInvolution L l → l ≠ z → l * z = z * l → L ∈ omegaNbr Ω K

end Defs

section Residual


@[expose] def PspNoA2Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' → PspNbhdDouble Ω K z → PspNoA2At Ω K z

end Residual

end CFSG.ClassicalInvolution.Q3.Q3AM
