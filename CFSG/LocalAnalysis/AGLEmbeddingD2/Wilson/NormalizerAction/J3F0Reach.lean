module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Mat

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Matrix

@[expose] def addNew (acc : List (Matrix (Fin 4) (Fin 4) (ZMod 3)))
    (l : List (Matrix (Fin 4) (Fin 4) (ZMod 3))) : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  l.foldl (fun a s => if a.any (eqM s) then a else a ++ [s]) acc

@[expose] def genS : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) := [actMat 0, actMat 1, actMat 2]

@[expose] def reachStep (l : List (Matrix (Fin 4) (Fin 4) (ZMod 3))) :
    List (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  addNew l (genS.flatMap fun g => l.map (mulM g))

@[expose] def reachN : ℕ → List (Matrix (Fin 4) (Fin 4) (ZMod 3))
  | 0 => [1]
  | n + 1 => reachStep (reachN n)

@[expose] def reachChk : Bool := matS.all fun s => (reachN 12).any (eqM s)

theorem reachChk_true : reachChk = true := by decide +kernel

theorem addNew_mem {P : Matrix (Fin 4) (Fin 4) (ZMod 3) → Prop}
    {acc l : List (Matrix (Fin 4) (Fin 4) (ZMod 3))} (hacc : ∀ s ∈ acc, P s) (hl : ∀ s ∈ l, P s) :
    ∀ s ∈ addNew acc l, P s := by
  unfold addNew
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x l ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro s hs
      split_ifs at hs with hx
      · exact hacc s hs
      · rcases List.mem_append.1 hs with h | h
        · exact hacc s h
        · rw [List.mem_singleton.1 h]; exact hl x (by simp)
    · intro s hs; exact hl s (by simp [hs])

theorem reachN_mem (n : ℕ) : ∀ s ∈ reachN n,
    s ∈ Submonoid.closure {actMat 0, actMat 1, actMat 2} := by
  induction n with
  | zero =>
    intro s hs
    rw [reachN, List.mem_singleton] at hs
    rw [hs]; exact Submonoid.one_mem _
  | succ n ih =>
    intro s hs
    refine addNew_mem (P := fun s => s ∈ Submonoid.closure {actMat 0, actMat 1, actMat 2}) ih ?_ s hs
    intro s hs
    simp only [genS, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_map] at hs
    rcases hs with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;>
      rw [mulM_eq] <;> refine Submonoid.mul_mem _ (Submonoid.subset_closure (by simp)) (ih t ht)

theorem matS_mem_closure : ∀ s ∈ matS, s ∈ Submonoid.closure {actMat 0, actMat 1, actMat 2} := by
  have h := reachChk_true
  simp only [reachChk, List.all_eq_true, List.any_eq_true, eqM_iff] at h
  intro s hs
  obtain ⟨t, ht, hts⟩ := h s hs
  rw [hts]
  exact reachN_mem 12 t ht

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
