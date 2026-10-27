module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.GF2Type.Smith1979.GammaU

@[expose] def extDFS {α : Type} (cand : List α → List α) : ℕ → List α → List (List α)
  | 0, pre => [pre]
  | k + 1, pre => (cand pre).flatMap fun c => extDFS cand k (pre ++ [c])

theorem mem_extDFS {α : Type} (cand : List α → List α) :
    ∀ (tail pre : List α),
      (∀ (i : ℕ) (hi : i < tail.length), tail[i] ∈ cand (pre ++ tail.take i)) →
        pre ++ tail ∈ extDFS cand tail.length pre
  | [], pre, _ => by simp [extDFS]
  | c :: tail, pre, h => by
    simp only [List.length_cons, extDFS, List.mem_flatMap]
    refine ⟨c, by
      have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero, List.take_zero, List.append_nil] at h0
      exact h0, ?_⟩
    have := mem_extDFS cand tail (pre ++ [c]) fun i hi => by
      have h' := h (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.append_assoc] using h'
    simpa [List.append_assoc] using this

end CFSG.GF2Type.Smith1979.GammaU
