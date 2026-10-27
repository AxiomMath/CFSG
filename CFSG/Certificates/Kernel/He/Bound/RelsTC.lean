module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held
public import CFSG.Certificates.Kernel.He.Bound.Rels

public section

namespace CFSG.KC.HeB

open TauCeti

@[expose] def code (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNat : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => code l + 256 * wordNat w

@[expose] def ent (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wordNat w

@[expose] def lettersLit : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)],
   List.replicate 7 (1, true),
   (List.replicate 17 [(0, true), (1, true)]).flatten,
   (List.replicate 6 [(0, false), (1, false), (0, true), (1, true)]).flatten,
   (List.replicate 5 [(0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true),
     (1, true)]).flatten,
   [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
    (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true),
    (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)]]

theorem relatorLetters_eq : Sporadic.hePresentation.relatorLetters = lettersLit := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.hePresentation_transcribed]
  simp [FreeGroup.invRev, lettersLit]

theorem relatorLetters_ent : Sporadic.hePresentation.relatorLetters.map ent = list := by
  rw [relatorLetters_eq]
  decide

end CFSG.KC.HeB

end
