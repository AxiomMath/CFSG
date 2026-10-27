module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.A6

open CFSG.Sporadic.Schreier

@[expose] def evenOrd (g : Equiv.Perm (Fin 10)) : Bool := orderIs g 2 || orderIs g 4

@[expose] def wit (κ : Equiv.Perm (Fin 10)) (H : List (Equiv.Perm (Fin 10))) : Bool :=
  H.any fun g => H.any fun h => evenOrd ((κ * g * κ⁻¹ * g⁻¹) * (h * (κ * g * κ⁻¹ * g⁻¹) * h⁻¹))

@[expose] def a6check (LA LP : List (Equiv.Perm (Fin 10))) : Bool :=
  (LP.all fun g => orderIs g 1 || orderIs g 2 || orderIs g 3 || orderIs g 4 || orderIs g 5) &&
  (LA.all fun τ => bif decide (τ * τ = 1 ∧ τ ≠ 1) then
    (let H := LP.filter fun κ => decide (τ * κ = κ * τ)
     H.all fun κ => bif orderIs κ 3 then wit κ H else true)
   else true)

end CFSG.GH74.GLS.C3.Layer1.EndN.A6
