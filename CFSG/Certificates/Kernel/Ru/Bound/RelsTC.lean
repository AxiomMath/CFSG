module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import CFSG.Certificates.Kernel.Ru.Bound.Rels

public section

namespace CFSG.KC.RuB

open TauCeti

@[expose] def code (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNat : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wordNat w

theorem relatorLetters_ent : Sporadic.ruPresentation.relatorLetters.map ent = list := by
  rw [Sporadic.ruPresentation_relatorLetters]
  simp only [List.map_cons, List.map_nil, list, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end CFSG.KC.RuB

end
