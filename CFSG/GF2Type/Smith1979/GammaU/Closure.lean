module

public import Aesop.BuiltinRules
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.GF2Type.Smith1979.GammaU

@[expose] def bfsRound {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ))
    (frontier : List σ) (seen : Std.HashSet κ) : List σ × Std.HashSet κ :=
  (frontier.flatMap fun s => fs.map fun f => f s).foldl
    (fun (acc : List σ × Std.HashSet κ) t =>
      if acc.2.contains (key t) then acc else (t :: acc.1, acc.2.insert (key t)))
    ([], seen)

@[expose] def bfsClosure {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ)) :
    ℕ → List σ → Std.HashSet κ → List σ → List σ
  | 0, frontier, _, visited => frontier ++ visited
  | fuel + 1, frontier, seen, visited =>
    let r := bfsRound key fs frontier seen
    if r.1.isEmpty then frontier ++ visited
    else bfsClosure key fs fuel r.1 r.2 (frontier ++ visited)

theorem bfsRound_inv {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ))
    {P : σ → Prop} (hP : ∀ f ∈ fs, ∀ s, P s → P (f s)) (frontier : List σ)
    (hfr : ∀ s ∈ frontier, P s) (seen : Std.HashSet κ) :
    ∀ t ∈ (bfsRound key fs frontier seen).1, P t := by
  unfold bfsRound
  have himg : ∀ t ∈ frontier.flatMap (fun s => fs.map fun f => f s), P t := by
    intro t ht
    simp only [List.mem_flatMap, List.mem_map] at ht
    obtain ⟨s, hs, f, hf, rfl⟩ := ht
    exact hP f hf s (hfr s hs)
  generalize frontier.flatMap (fun s => fs.map fun f => f s) = L at himg
  suffices h : ∀ (acc : List σ × Std.HashSet κ), (∀ t ∈ acc.1, P t) →
      ∀ t ∈ (L.foldl (fun (acc : List σ × Std.HashSet κ) t =>
        if acc.2.contains (key t) then acc else (t :: acc.1, acc.2.insert (key t))) acc).1, P t from
    h ([], seen) (by simp)
  induction L with
  | nil => exact fun acc hacc => hacc
  | cons a L ih =>
    intro acc hacc
    rw [List.foldl_cons]
    refine ih (fun t ht => himg t (List.mem_cons_of_mem a ht)) _ ?_
    split_ifs
    · exact hacc
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact himg t List.mem_cons_self
      · exact hacc t ht

theorem bfsClosure_inv {σ κ : Type} [BEq κ] [Hashable κ] (key : σ → κ) (fs : List (σ → σ))
    {P : σ → Prop} (hP : ∀ f ∈ fs, ∀ s, P s → P (f s)) :
    ∀ (fuel : ℕ) (frontier : List σ) (seen : Std.HashSet κ) (visited : List σ),
      (∀ s ∈ frontier, P s) → (∀ s ∈ visited, P s) →
        ∀ t ∈ bfsClosure key fs fuel frontier seen visited, P t
  | 0, frontier, _, visited, hfr, hvis => by
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hfr t ht
    · exact hvis t ht
  | fuel + 1, frontier, seen, visited, hfr, hvis => by
    intro t ht
    simp only [bfsClosure] at ht
    split_ifs at ht
    · rcases List.mem_append.1 ht with ht | ht
      · exact hfr t ht
      · exact hvis t ht
    · refine bfsClosure_inv key fs hP fuel _ _ _ (bfsRound_inv key fs hP frontier hfr seen)
        (fun s hs => ?_) t ht
      rcases List.mem_append.1 hs with hs | hs
      · exact hfr s hs
      · exact hvis s hs

end CFSG.GF2Type.Smith1979.GammaU
