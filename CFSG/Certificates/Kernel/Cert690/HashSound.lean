module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690

theorem idxMapOf_fold {E : List ℕ} (hE : E.Nodup) :
    ∀ k ≤ E.length, ∀ c d,
      ((List.range k).foldl (fun m i => m.insert (E.toArray[i]!) i) ({} : Std.HashMap ℕ ℕ)).getD
        c d = if c ∈ E.take k then E.idxOf c else d := by
  intro k
  induction k with
  | zero => intro _ c d; simp
  | succ k ih =>
    intro hk c d
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getD_insert, ih (by omega)]
    have hk' : k < E.length := by omega
    rw [List.getElem!_toArray, getElem!_pos E k hk', List.take_succ, List.getElem?_eq_getElem hk']
    simp only [Option.toList_some, List.mem_append, List.mem_singleton, beq_iff_eq]
    by_cases h : E[k] = c
    · subst h
      rw [if_pos rfl, if_pos (Or.inr rfl), hE.idxOf_getElem k hk']
    · rw [if_neg h]
      have : ¬ c = E[k] := fun e => h e.symm
      simp only [this, or_false]

theorem idxMapOf_getD {E : List ℕ} (hE : E.Nodup) (c : ℕ) :
    (idxMapOf E.toArray).getD c E.length = E.idxOf c := by
  unfold idxMapOf
  rw [List.size_toArray, idxMapOf_fold hE E.length le_rfl, List.take_length]
  split
  · rfl
  · rename_i h
    exact (List.idxOf_eq_length h).symm

theorem hashSet_fold (L : List ℕ) :
    ∀ (s : Std.HashSet ℕ) (F : Finset ℕ), (∀ x, s.contains x = true ↔ x ∈ F) → s.size = F.card →
      (∀ x, (L.foldl (fun s x => s.insert x) s).contains x = true ↔ x ∈ F ∪ L.toFinset) ∧
      (L.foldl (fun s x => s.insert x) s).size = (F ∪ L.toFinset).card := by
  induction L with
  | nil => intro s F h1 h2; simpa using ⟨h1, h2⟩
  | cons a L ih =>
    intro s F h1 h2
    rw [List.foldl_cons]
    have e : F ∪ (a :: L).toFinset = (insert a F) ∪ L.toFinset := by
      ext x
      simp [or_assoc, or_comm, or_left_comm]
    rw [e]
    refine ih _ _ (fun x => ?_) ?_
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, h1, beq_iff_eq, Finset.mem_insert]
      exact or_congr_left eq_comm
    · rw [Std.HashSet.size_insert, h2]
      by_cases ha : a ∈ F
      · have : a ∈ s := by
          rw [Std.HashSet.mem_iff_contains, h1]
          exact ha
        rw [if_pos this, Finset.insert_eq_of_mem ha]
      · have : a ∉ s := by
          rw [Std.HashSet.mem_iff_contains, h1]
          exact ha
        rw [if_neg this, Finset.card_insert_of_notMem ha]

theorem hashSetOfArray_contains (A : Array ℕ) (x : ℕ) :
    (hashSetOfArray A).contains x = A.toList.contains x := by
  have h := (hashSet_fold A.toList ∅ ∅ (by simp) (by simp)).1 x
  unfold hashSetOfArray
  rw [← Array.foldl_toList]
  rw [Bool.eq_iff_iff, h]
  simp

theorem hashSetOfArray_size (A : Array ℕ) :
    (hashSetOfArray A).size = A.toList.toFinset.card := by
  have h := (hashSet_fold A.toList ∅ ∅ (by simp) (by simp)).2
  unfold hashSetOfArray
  rw [← Array.foldl_toList, h, Finset.empty_union]

end CFSG.KC.C690

end
