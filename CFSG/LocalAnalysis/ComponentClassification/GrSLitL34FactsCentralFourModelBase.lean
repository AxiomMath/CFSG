
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

def Z0 : Subgroup (Equiv.Perm (Fin 42)) :=
  centralizer (T0 : Set (Equiv.Perm (Fin 42))) ⊓ T0

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

noncomputable def omegaZ (q : E →* Equiv.Perm (Fin 42))
    (l : Cover →* E) (β : E ≃* E) : Subgroup E :=
  zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ (fixT0 q β ⊓ q.ker))

end CFSG.ComponentClassification.GrSLit.L34Facts
