module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.McLaughlin
public import CFSG.Certificates.Kernel.McL.TC

public section

namespace CFSG.KC.McL.TC

open TauCeti

@[expose] def code (l : ℕ × Bool) : Nat := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNat : List (ℕ × Bool) → Nat
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (ℕ × Bool)) : Nat := 4 * w.length + 4096 * wordNat w

theorem relators_eq : (Sporadic.mclPresentation.relatorLetters.map ent) = list := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.mclPresentation_transcribed]
  simp only [List.map_cons, List.map_nil, Relator.toWord_gen, Relator.toWord_inv,
    Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_comm]
  decide

end CFSG.KC.McL.TC

end
