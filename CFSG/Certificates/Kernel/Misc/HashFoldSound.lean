module

public import CFSG.Certificates.Kernel.G2Three.IndexMap
public import Certificates.Data.RudvalisFF81Sp8Codes

public section

namespace CFSG.KC.HashFold

open CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

variable {α β κ : Type*} [BEq κ] [LawfulBEq κ] [Hashable κ]

theorem get?_foldl_insert (f : α → κ) (g : α → β) (l : List α) (m : Std.HashMap κ β) (k : κ) :
    (l.foldl (fun m a => m.insert (f a) (g a)) m).get? k =
      ((l.reverse.find? fun a => f a == k).map g).or (m.get? k) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.get?_insert, ih,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.find?_cons]
    cases h : f a == k <;> simp

theorem get?_foldl_insert_empty (f : α → κ) (g : α → β) (l : List α) (k : κ) :
    (l.foldl (fun m a => m.insert (f a) (g a)) (∅ : Std.HashMap κ β)).get? k =
      (l.reverse.find? fun a => f a == k).map g := by
  rw [get?_foldl_insert]
  simp

theorem get?_foldl_insert_eq_some {f : α → κ} {g : α → β} {l : List α} {k : κ} {v : β}
    (h : (l.foldl (fun m a => m.insert (f a) (g a)) (∅ : Std.HashMap κ β)).get? k = some v) :
    ∃ a ∈ l, f a = k ∧ g a = v := by
  rw [get?_foldl_insert_empty, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  have hk : (f a == k) = true := List.find?_some (p := fun a => f a == k) ha
  exact ⟨a, List.mem_reverse.1 (List.mem_of_find?_eq_some ha), beq_iff_eq.1 hk, rfl⟩

theorem get?_foldl_insert_eq_none {f : α → κ} {g : α → β} {l : List α} {k : κ} :
    (l.foldl (fun m a => m.insert (f a) (g a)) (∅ : Std.HashMap κ β)).get? k = none ↔
      ∀ a ∈ l, f a ≠ k := by
  rw [get?_foldl_insert_empty, Option.map_eq_none_iff, List.find?_eq_none]
  simp

theorem get?_foldl_insert_of_last {f : α → κ} {g : α → β} {l₁ l₂ : List α} {a : α} {k : κ}
    (ha : f a = k) (h₂ : ∀ b ∈ l₂, f b ≠ k) :
    ((l₁ ++ a :: l₂).foldl (fun m a => m.insert (f a) (g a)) (∅ : Std.HashMap κ β)).get? k =
      some (g a) := by
  have hn : (l₂.reverse.find? fun b => f b == k) = none :=
    List.find?_eq_none.2 fun b hb => by simpa using h₂ b (List.mem_reverse.1 hb)
  rw [get?_foldl_insert_empty]
  simp [List.reverse_append, List.find?_append, hn, ha]

theorem get?_range_foldl {K : ℕ → κ} {n t : ℕ} {k : κ}
    (h : ((List.range n).foldl (fun m t => m.insert (K t) t) (∅ : Std.HashMap κ ℕ)).get? k =
      some t) : t < n ∧ K t = k := by
  obtain ⟨a, ha, hk, rfl⟩ := get?_foldl_insert_eq_some (f := K) (g := fun t => t) h
  exact ⟨List.mem_range.1 ha, hk⟩

theorem isSome_get?_range_foldl {K : ℕ → κ} {n : ℕ} {k : κ} :
    (((List.range n).foldl (fun m t => m.insert (K t) t) (∅ : Std.HashMap κ ℕ)).get? k).isSome ↔
      ∃ t < n, K t = k := by
  rw [← Option.ne_none_iff_isSome, Ne, get?_foldl_insert_eq_none (f := K) (g := fun t => t)]
  simp

theorem get?_ofList (l : List (κ × β)) (k : κ) :
    (Std.HashMap.ofList l).get? k = (l.reverse.find? fun p => p.1 == k).map Prod.snd := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.ofList_eq_insertMany_empty,
    Std.HashMap.getElem?_insertMany_list, List.findSomeRev?_eq_findSome?_reverse]
  simp only [Std.HashMap.getElem?_empty, Option.or_none]
  generalize l.reverse = l'
  induction l' with
  | nil => rfl
  | cons p l' ih =>
    rw [List.find?_cons]
    cases h : p.1 == k
    · rw [List.findSome?_cons_of_isNone (by simp [h]), ih]
    · rw [List.findSome?_cons_of_isSome (by simp [h])]
      simp [h]

theorem get?_ofList_eq_some {l : List (κ × β)} {k : κ} {v : β}
    (h : (Std.HashMap.ofList l).get? k = some v) : (k, v) ∈ l := by
  rw [get?_ofList, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hk : (p.1 == k) = true := List.find?_some (p := fun q : κ × β => q.1 == k) hp
  rw [← beq_iff_eq.1 hk]
  exact List.mem_reverse.1 (List.mem_of_find?_eq_some hp)

theorem get?_ofList_eq_none {l : List (κ × β)} {k : κ} :
    (Std.HashMap.ofList l).get? k = none ↔ ∀ p ∈ l, p.1 ≠ k := by
  rw [get?_ofList, Option.map_eq_none_iff, List.find?_eq_none]
  simp

theorem get?_ofList_of_last {l₁ l₂ : List (κ × β)} {k : κ} {v : β}
    (h₂ : ∀ p ∈ l₂, p.1 ≠ k) : (Std.HashMap.ofList (l₁ ++ (k, v) :: l₂)).get? k = some v := by
  have hn : (l₂.reverse.find? fun p => p.1 == k) = none :=
    List.find?_eq_none.2 fun p hp => by simpa using h₂ p (List.mem_reverse.1 hp)
  rw [get?_ofList]
  simp [List.reverse_append, List.find?_append, hn]

theorem getD_ofList_of_last {l₁ l₂ : List (κ × β)} {k : κ} {v d : β}
    (h₂ : ∀ p ∈ l₂, p.1 ≠ k) : (Std.HashMap.ofList (l₁ ++ (k, v) :: l₂)).getD k d = v := by
  rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, get?_ofList_of_last h₂]
  rfl

theorem contains_ofList_iff (l : List κ) (k : κ) :
    (Std.HashSet.ofList l).contains k = true ↔ k ∈ l := by
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem]

theorem found_indexMap_iff_mem {es : Array (List ℕ)} {y : List ℕ} :
    found es (indexMap es) y = true ↔ y ∈ es := by
  rw [CFSG.KC.G2Three.found_indexMap, Array.mem_iff_getElem]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]; rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]; rfl⟩

theorem cmapS_get? {es inv : Array (List ℕ)} {a x : List ℕ} {t : ℕ}
    (h : (cmapS es inv a).get? x = some t) :
    t < es.size ∧ mulS (mulS (es.getD t []) a) (inv.getD t []) = x :=
  get?_range_foldl h

theorem isSome_cmapS {es inv : Array (List ℕ)} {a x : List ℕ} :
    ((cmapS es inv a).get? x).isSome ↔
      ∃ t < es.size, mulS (mulS (es.getD t []) a) (inv.getD t []) = x :=
  isSome_get?_range_foldl

theorem cfoundS_spec {es : Array (List ℕ)} {m : Std.HashMap (List ℕ) ℕ} {a x : List ℕ}
    (h : cfoundS es m a x = true) :
    ∃ t < es.size, mulS (es.getD t []) a = mulS x (es.getD t []) := by
  unfold cfoundS at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨t, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

theorem cfoundS_cmapS_iff {es inv : Array (List ℕ)} {a x : List ℕ}
    (hc : ∀ t < es.size, mulS (mulS (es.getD t []) a) (inv.getD t []) = x →
      mulS (es.getD t []) a = mulS x (es.getD t [])) :
    cfoundS es (cmapS es inv a) a x = true ↔
      ∃ t < es.size, mulS (mulS (es.getD t []) a) (inv.getD t []) = x := by
  unfold cfoundS
  constructor
  · intro h
    split at h
    · rename_i t ht
      exact ⟨t, cmapS_get? ht⟩
    · exact absurd h Bool.false_ne_true
  · intro h
    have hs := isSome_cmapS.2 h
    cases hm : (cmapS es inv a).get? x with
    | none => rw [hm] at hs; cases hs
    | some t =>
      obtain ⟨ht, e⟩ := cmapS_get? hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨ht, hc t ht e⟩

end CFSG.KC.HashFold

end
