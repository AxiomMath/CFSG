module

public import CFSG.Certificates.Kernel.GilmanCensus.MkDataSound
public import CFSG.Certificates.Kernel.GilmanCensus.RootsSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

theorem forIn_yieldL {α β : Type} (g : β → α → β) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List α) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact forIn_yieldL g f hf l (g init a)

theorem forIn_yieldA {α β : Type} (g : β → α → β) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) (xs : Array α) (init : β) :
    forIn (m := Id) xs init f = xs.toList.foldl g init := by
  rw [← Array.forIn_toList]
  exact forIn_yieldL g f hf _ init

theorem rev_ind {α : Type} {P : List α → Prop} (h0 : P []) (hs : ∀ l y, P l → P (l ++ [y])) :
    ∀ l, P l := by
  have : ∀ l : List α, P l.reverse := by
    intro l
    induction l with
    | nil => exact h0
    | cons y l ih =>
      rw [List.reverse_cons]
      exact hs _ y ih
  intro l
  simpa using this l.reverse

theorem idxsK_snoc {α : Type} [BEq α] [LawfulBEq α] (x y : α) : ∀ (l : List α) (k : Nat),
    idxsK x (l ++ [y]) k = idxsK x l k ++ (if y == x then [k + l.length] else [])
  | [], k => by
    simp only [List.nil_append, idxsK, List.length_nil, Nat.add_zero]
  | z :: l, k => by
    simp only [List.cons_append, idxsK, List.length_cons]
    rw [idxsK_snoc x y l (k + 1), Nat.add_assoc, Nat.add_comm 1 l.length]
    split <;> rfl

theorem dedupK_snoc {α : Type} [BEq α] (l : List α) (y : α) :
    dedupK (l ++ [y]) = if (dedupK l).contains y then dedupK l else dedupK l ++ [y] := by
  unfold dedupK
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem idxsK_nil {α : Type} [BEq α] [LawfulBEq α] (x : α) : ∀ (l : List α) (k : Nat),
    (l.contains x = false) → idxsK x l k = []
  | [], _, _ => rfl
  | y :: l, k, h => by
    simp only [List.contains_cons, Bool.or_eq_false_iff] at h
    simp only [idxsK]
    have : (y == x) = false := by
      rw [beq_eq_false_iff_ne]
      have := h.1
      rw [beq_eq_false_iff_ne] at this
      exact fun e => this e.symm
    rw [this]
    exact idxsK_nil x l (k + 1) h.2

theorem dedupK_contains {α : Type} [BEq α] [LawfulBEq α] (x : α) : ∀ (l : List α),
    (dedupK l).contains x = l.contains x := by
  refine rev_ind rfl ?_
  intro l y ih
  rw [dedupK_snoc]
  split
  · rename_i h
    rw [ih, List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false]
    by_cases e : x = y
    · subst e
      rw [ih] at h
      simpa using h
    · have : (x == y) = false := by rw [beq_eq_false_iff_ne]; exact e
      simp [this]
  · rw [contains_snoc', contains_snoc', ih]

@[expose] def grpStep (st : HashMap IVec (Array Nat) × Array IVec) (p : IVec × Nat) :
    HashMap IVec (Array Nat) × Array IVec :=
  ((st.1.insert p.1 ((st.1.getD p.1 #[]).push p.2)),
    if (!st.1.contains p.1) = true then st.2.push p.1 else st.2)

theorem arr_beqI (s v : Array Int) : (s == v) = (v.toList == s.toList) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Array.toList_inj]
  exact eq_comm

theorem groups_fold : ∀ (l : List IVec),
    let st := (l.zip (List.range l.length)).foldl grpStep (∅, #[])
    LLI st.2 = dedupK (l.map Array.toList) ∧
      ∀ v : IVec, (st.1.getD v #[]).toList = idxsK v.toList (l.map Array.toList) 0 ∧
        st.1.contains v = (l.map Array.toList).contains v.toList := by
  refine rev_ind ?_ ?_
  · simp only [List.length_nil, List.range_zero, List.zip_nil_right, List.foldl_nil]
    refine ⟨rfl, fun v => ⟨?_, ?_⟩⟩
    · simp [idxsK]
    · simp
  · intro l y ih
    dsimp only at ih ⊢
    rw [List.length_append, List.length_singleton, List.range_succ, List.zip_append (by simp),
      List.foldl_append, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := ih
    generalize (l.zip (List.range l.length)).foldl grpStep (∅, #[]) = st at h1 h2
    unfold grpStep
    dsimp only
    refine ⟨?_, fun v => ⟨?_, ?_⟩⟩
    · rw [List.map_append, List.map_singleton, dedupK_snoc, dedupK_contains, ← (h2 y).2]
      cases st.1.contains y
      · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        rw [LLI_push, h1]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact h1
    · rw [HashMap.getD_insert, List.map_append, List.map_singleton, idxsK_snoc, List.length_map,
        Nat.zero_add, arr_beqI]
      by_cases e : y.toList = v.toList
      · have e' : (v.toList == y.toList) = true := by rw [beq_iff_eq]; exact e.symm
        have e'' : (y.toList == v.toList) = true := by rw [beq_iff_eq]; exact e
        rw [e', e'']
        simp only [↓reduceIte, Array.toList_push]
        have hv : v = y := Array.toList_inj.mp e.symm
        subst hv
        rw [(h2 v).1]
      · have e' : (v.toList == y.toList) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h => e h.symm
        have e'' : (y.toList == v.toList) = false := by rw [beq_eq_false_iff_ne]; exact e
        rw [e', e'']
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
        exact (h2 v).1
    · rw [HashMap.contains_insert, (h2 v).2, List.map_append, List.map_singleton, contains_snoc',
        arr_beqI]

@[expose] def scaledK (H : List (List Nat)) : List (List Nat) :=
  H.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3]

theorem hs_fold (H : Array (Array Nat)) :
    Id.run (forIn H (∅ : HashSet (Array Nat)) fun h hs =>
      pure (ForInStep.yield (Id.run (forIn [1, 2] hs fun s hs =>
        pure (ForInStep.yield (hs.insert (h.map fun x => x * s % 3)))))))=
      ((H.toList.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3]).foldl
        (fun S x => S.insert x) ∅) := by
  rw [← Array.forIn_toList, List.forIn_pure_yield_eq_foldl, List.foldl_flatMap]
  rfl

theorem scaled_map (H : Array (Array Nat)) :
    (H.toList.flatMap fun h => [h.map fun x => x * 1 % 3, h.map fun x => x * 2 % 3]).map Array.toList =
      scaledK (LL H) := by
  simp [scaledK, LL, List.map_flatMap, List.flatMap_map]

theorem G_eq (B : Array (Array Int)) (R : Array IVec) :
    LLI (R.map fun r => R.map fun s => gramB B r s) =
      (LLI R).map fun r => (LLI R).map fun s => gramK (LLI B) r s := by
  simp [LLI, gramB_eq, Function.comp_def]

theorem fhOk_eq (F H : Array (Array Nat)) (G : Array (Array Int)) (g : Nat → Nat → Int)
    (hG : ∀ i j, G[i]![j]! = g i j) (N : Nat) (ok : Bool) :
    Id.run (forIn [0:N] ok fun i ok => do
      let r ← forIn [0:N] ok fun j ok =>
        if ((dot3 F[i]! H[j]! : Int) != 2 * G[i]![j]! / G[j]![j]! % 3) = true then
          pure (ForInStep.yield false)
        else pure (ForInStep.yield ok)
      pure (ForInStep.yield r)) = fhOkK (LL F) (LL H) g N ok := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  unfold fhOkK
  rw [forIn_yield (fun ok i => (List.range' 0 N).foldl (fun ok j =>
    if ((dot3K ((LL F).getD i []) ((LL H).getD j []) : Int) != 2 * g i j / g j j % 3) = true
    then false else ok) ok) _ (fun i ok => by
      simp only [Id.run, bind, pure]
      rw [forIn_yield (fun ok j =>
        if ((dot3K ((LL F).getD i []) ((LL H).getD j []) : Int) != 2 * g i j / g j j % 3) = true
        then false else ok) _ (fun j ok => by
          rw [dot3_eq, getRow, getRow, hG, hG]
          split <;> simp_all)])]
  rfl

end Certificates.GilmanCensusK

end
