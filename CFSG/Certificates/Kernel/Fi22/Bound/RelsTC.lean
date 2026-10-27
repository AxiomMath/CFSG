module

public import CFSG.Certificates.Kernel.Orders.Fi22.RelsBind
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels

public section

namespace CFSG.KC.Fi22B

open TauCeti

@[expose] def code (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNat : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wordNat w

theorem relatorLetters_ent : Sporadic.fi22Presentation.relatorLetters.map ent = list := by
  rw [CFSG.KD.OrdFi22.rels_eq]
  simp only [CFSG.KD.OrdFi22.rels, List.map_cons, List.map_nil, list, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end CFSG.KC.Fi22B

end
