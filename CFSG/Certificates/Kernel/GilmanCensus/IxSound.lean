module

public import CFSG.Certificates.Kernel.GilmanCensus.RelSound
public import CFSG.Certificates.Kernel.GilmanCensus.RootsSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem idxI_snoc (v x : List Int) : ∀ (l : List (List Int)) (k : Nat),
    idxI v (l ++ [x]) k = match idxI v l k with
      | some j => some j
      | none => if x == v then some (k + l.length) else none
  | [], k => by simp [idxI]
  | r :: l, k => by
    simp only [List.cons_append, idxI]
    split
    · rfl
    · rw [idxI_snoc v x l (k + 1)]
      simp only [List.length_cons]
      cases idxI v l (k + 1) with
      | some j => rfl
      | none =>
        simp only
        rw [Nat.add_assoc, Nat.add_comm 1]

theorem idxI_none (v : List Int) : ∀ (l : List (List Int)) (k : Nat), v ∉ l → idxI v l k = none
  | [], _, _ => rfl
  | r :: l, k, h => by
    simp only [idxI]
    have hr : (r == v) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact h (e ▸ List.mem_cons_self)
    rw [hr]
    exact idxI_none v l (k + 1) (fun hm => h (List.mem_cons_of_mem r hm))

theorem ix_prefix (R : Array IVec) (hnd : (LLI R).Nodup) (v : IVec) : ∀ k, k ≤ R.size →
    ((List.range' 0 k).foldl (fun (ix : HashMap IVec Nat) i => ix.insert R[i]! i) ∅)[v]? =
      idxI v.toList ((LLI R).take k) 0
  | 0, _ => by simp [idxI]
  | k + 1, hk => by
    rw [List.range'_concat, Nat.one_mul, Nat.zero_add, List.foldl_append, List.foldl_cons,
      List.foldl_nil, HashMap.getElem?_insert, ix_prefix R hnd v k (by omega)]
    have hkl : k < (LLI R).length := by rw [length_LLI]; omega
    have hRk : (LLI R)[k] = (R[k]!).toList := by
      simp [LLI, getElem!_pos R k (by omega)]
    rw [List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some, idxI_snoc,
      List.length_take_of_le (by omega), Nat.zero_add, hRk, arr_beq]
    by_cases e : v.toList = (R[k]!).toList
    · have hnot : v.toList ∉ (LLI R).take k := by
        rw [e, ← hRk]
        intro hm
        have h2 := hnd
        rw [← List.take_append_drop k (LLI R), List.nodup_append] at h2
        exact h2.2.2 _ hm _ (by rw [List.drop_eq_getElem_cons hkl]; exact List.mem_cons_self) rfl
      rw [idxI_none _ _ 0 hnot, e]
    · have e' : ((R[k]!).toList == v.toList) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e h.symm
      have e'' : (v.toList == (R[k]!).toList) = false := by
        rw [beq_eq_false_iff_ne]
        exact e
      rw [e', e'']
      cases idxI v.toList (List.take k (LLI R)) 0 <;> rfl

theorem ix_fold (R : Array IVec) (hnd : (LLI R).Nodup) (v : IVec) :
    (Id.run (forIn [0:R.size] (∅ : HashMap IVec Nat) fun i ix =>
      pure (ForInStep.yield (ix.insert R[i]! i))))[v]? = idxI v.toList (LLI R) 0 := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure]
  rw [ix_prefix R hnd v R.size (Nat.le_refl _), List.take_of_length_le (by rw [length_LLI]; exact Nat.le_refl _)]

end Certificates.GilmanCensusK

end
