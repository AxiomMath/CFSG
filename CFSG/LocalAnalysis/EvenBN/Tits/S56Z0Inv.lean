module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

@[expose] def S56Z0Inv (d : Data G) : Prop := ∀ z₀ : G, d.S56Z0 z₀ → z₀ * z₀ = 1

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
