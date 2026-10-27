module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8A6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel
public import CFSG.GH74.KGroups.A6
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.A6

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

local notation "P10" => Equiv.Perm (Fin 10)

namespace A6

@[expose] def fixCount (LP : List P10) (s : P10) : ℕ :=
  (LP.filter fun g => decide (g * s = s * g)).length

@[expose, noinline] def expCheck (LA : List P10) : Bool :=
  LA.all fun g => decide (g ^ 120 = 1)

@[expose, noinline] def diagCheck (LA LP : List P10) : Bool :=
  LA.all fun s => !(decide (s * s = 1)) || decide (fixCount LP s = 10) ||
    LA.all fun o => !(decide (o * s = s * o)) || decide (o = 1) || !(decide (o ^ 15 = 1)) ||
      LP.any fun n => decide (n * s = s * n) && !(decide ((o * n * o⁻¹ * n⁻¹) ^ 15 = 1))

@[expose, noinline] def centCountC (L C : List P10) : ℕ :=
  (L.filter fun g => C.all fun y => decide (y * g = g * y)).length

@[expose] def centCount (L LP : List P10) (x : P10) : ℕ :=
  centCountC L (LP.filter fun y => decide (x * y = y * x))

@[expose, noinline] def innerCheck (LA LP : List P10) : Bool :=
  LP.all fun x => !(decide (x * x = 1)) || decide (x = 1) ||
    (decide (fixCount LP x = 8) &&
      LA.all (fun a => !(decide (a * x = x * a)) || decide (a ^ 32 = 1)) &&
      decide (centCount LA LP x = 4) && decide (centCount LP LP x = 2))

@[expose, noinline] def noCommCheck (LA LP : List P10) : Bool :=
  LA.all fun s₁ => !(decide (s₁ * s₁ = 1)) || !(decide (fixCount LP s₁ = 10)) ||
    LA.all fun s₂ => !(decide (s₂ * s₂ = 1)) || LP.contains s₂ ||
      !(decide (fixCount LP s₂ % 8 = 0)) || !(decide (s₁ * s₂ = s₂ * s₁))

end A6

open A6

variable {J₀ : Type} [Group J₀]

end CFSG.ComponentClassification.CatFactsSmall
