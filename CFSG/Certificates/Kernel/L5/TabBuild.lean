module

public import CFSG.GH74.GLS.C3.Layer2.L5C2b
public import CFSG.Certificates.Kernel.L5.Tables

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

open CFSG.GH74.GLS.C3.Layer2.L5

variable {M : Type} [Group M]

theorem foldl_push_map_eq {α β : Type} (f : α → β) (l : List α) (t : Array β) :
    l.foldl (fun t x => t.push (f x)) t = t ++ (l.map f).toArray := by
  induction l generalizing t with
  | nil => simp
  | cons x l ih => simp [ih]

theorem foldl_append_flatMap_eq {α β : Type} (g : α → List β) (l : List α) (t : Array β) :
    l.foldl (fun t a => t ++ (g a).toArray) t = t ++ (l.flatMap g).toArray := by
  induction l generalizing t with
  | nil => simp
  | cons x l ih => simp [ih, Array.append_assoc]

theorem buildTab_eq (elems : List M) (code : M → Nat) :
    buildTab elems code = ((List.range elems.length).flatMap fun a =>
      (List.range elems.length).map fun b =>
        (elems.map code).idxOf (code (elems.getD a 1 * elems.getD b 1))).toArray := by
  unfold buildTab
  simp [Id.run, foldl_push_map_eq, foldl_append_flatMap_eq, KT.getD_toArray, ← List.range_eq_range']
  rfl

theorem buildTab_getD (elems : List M) (code : M → Nat) {a b : Nat} (ha : a < elems.length)
    (hb : b < elems.length) :
    (buildTab elems code).getD (a * elems.length + b) 0 =
      (elems.map code).idxOf (code (elems.getD a 1 * elems.getD b 1)) := by
  rw [buildTab_eq, KT.getD_toArray]
  exact KT.getD_flatMap_range _ _ (fun a b => (elems.map code).idxOf
    (code (elems.getD a 1 * elems.getD b 1))) 0 ha hb

theorem idxOf_code_spec {elems : List M} {code : M → Nat} (hn : (elems.map code).Nodup) {m : M}
    (hm : m ∈ elems) :
    (elems.map code).idxOf (code m) < elems.length ∧
      elems.getD ((elems.map code).idxOf (code m)) 1 = m := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
  have e : code elems[k] = (elems.map code)[k]'(by simpa using hk) := by simp
  rw [e, List.Nodup.idxOf_getElem hn, List.getD_eq_getElem _ _ hk]
  exact ⟨hk, rfl⟩

theorem tabCheck_build [DecidableEq M] {elems : List M} {code : M → Nat} (hc : ∀ m, m ∈ elems)
    (hn : (elems.map code).Nodup) :
    tabCheck elems code (buildTab elems code) (buildInv elems code) (buildOne elems code) =
      true := by
  simp only [tabCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hn, fun a ha b hb => ?_⟩, fun a ha => ?_⟩, ?_⟩, ?_⟩
  · rw [buildTab_getD elems code ha hb]
    exact idxOf_code_spec hn (hc _)
  · have e : (buildInv elems code).getD a 0 = (elems.map code).idxOf (code (elems.getD a 1)⁻¹) := by
      unfold buildInv
      rw [KT.getD_toArray, List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map,
        List.getD_eq_getElem _ _ ha]
    rw [e]
    exact idxOf_code_spec hn (hc _)
  · exact (idxOf_code_spec hn (hc 1)).1
  · exact (idxOf_code_spec hn (hc 1)).2

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
