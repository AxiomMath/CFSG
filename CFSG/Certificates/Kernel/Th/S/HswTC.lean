module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Thompson
public import CFSG.Certificates.Kernel.Th.S.Hsw

public section

namespace CFSG.KC.Th.Hsw

open TauCeti

@[expose] def code (l : Fin 8 × Bool) : Nat := 2 * l.1.val + (if l.2 then 0 else 1)

@[expose] def wordNat : List (Fin 8 × Bool) → Nat
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (Fin 8 × Bool)) : Nat := 4 * w.length + 4096 * wordNat w

theorem relatorList_eq : (Sporadic.Thompson.relatorList.map fun r => ent r.toWord) = list := by
  simp only [Sporadic.Thompson.relatorList, Sporadic.Thompson.relatorsOne,
    Sporadic.Thompson.relatorsTwo, Sporadic.Thompson.relatorsThree, Sporadic.Thompson.relatorsFour,
    Sporadic.Thompson.relatorsFive, Sporadic.Thompson.relatorsSix, Relator.commInvInv, Relator.conj,
    Relator.div, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
    Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

theorem relators_eq : (Sporadic.Thompson.presentation.relators.map ent) = list :=
  (congrArg (List.map ent) (GroupPresentation.relators_def _)).trans
    ((List.map_map ..).trans relatorList_eq)

end CFSG.KC.Th.Hsw

end
