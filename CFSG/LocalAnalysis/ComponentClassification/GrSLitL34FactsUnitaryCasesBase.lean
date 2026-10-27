
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E]

theorem card_ker_restrict (q : E →* Equiv.Perm (Fin 42)) (β : E ≃* E) :
    Nat.card (q.comp (fixT0 q β).subtype).ker = Nat.card ↥(fixT0 q β ⊓ q.ker) :=
  Nat.card_congr
    { toFun := fun e => ⟨e.1.1, e.1.2, e.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CFSG.ComponentClassification.GrSLit.L34Facts
