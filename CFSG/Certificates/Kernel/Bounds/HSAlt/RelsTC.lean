module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HigmanSims
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels

public section

namespace CFSG.KC.HSK

open TauCeti

theorem rels_eq : Sporadic.hsPresentation.relatorLetters = relsLit := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.hsPresentation_transcribed]
  simp [FreeGroup.invRev, relsLit]

@[expose] def code (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNat : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wordNat w

theorem relatorLetters_ent : Sporadic.hsPresentation.relatorLetters.map ent = list := by
  rw [rels_eq]
  simp only [relsLit, List.map_cons, List.map_nil, list, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end CFSG.KC.HSK

end
