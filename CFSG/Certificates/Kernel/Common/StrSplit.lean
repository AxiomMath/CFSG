module

public import Batteries.Data.String.Lemmas
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search
public import Std.Data.DTreeMap.Internal.Operations

public section

namespace CFSG.KC.Str

open String

theorem splitOnAux_of_valid (c : Char) (l m r acc) :
    splitOnAux (ofList (l ++ m ++ r)) (singleton c) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == c) r m.reverse).map ofList := by
  have hsep : singleton c = ofList ([] ++ [c]) := by rw [singleton_eq_ofList]; rfl
  have hg : Pos.Raw.get (singleton c) 0 = c := by
    rw [hsep]
    exact get_of_valid [] [c]
  have hn : Pos.Raw.next (singleton c) 0 = ⟨c.utf8Size⟩ := by
    rw [hsep]
    simpa using next_of_valid [] c []
  have he : (singleton c).rawEndPos ≤ ⟨c.utf8Size⟩ := by
    rw [hsep, rawEndPos_ofList]
    simp
  unfold splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨d, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa [-ofList_append] using
        (⟨get_of_valid (l ++ m) (d :: r), next_of_valid (l ++ m) d r⟩ : _ ∧ _), hg, hn, he]
    split <;> rename_i h
    · have hdc : d = c := by simpa using h
      subst hdc
      have hx : Pos.Raw.extract (ofList (l ++ (m ++ d :: r))) ⟨utf8Len l⟩
          ((⟨utf8Len l + utf8Len m + d.utf8Size⟩ : Pos.Raw).unoffsetBy ⟨d.utf8Size⟩) = ofList m := by
        have : ((⟨utf8Len l + utf8Len m + d.utf8Size⟩ : Pos.Raw).unoffsetBy ⟨d.utf8Size⟩) =
            ⟨utf8Len l + utf8Len m⟩ := by
          apply Pos.Raw.ext
          simp [Pos.Raw.byteIdx_unoffsetBy]
        rw [this]
        simpa using extract_of_valid l m (d :: r)
      simp only [hx]
      simpa [Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_of_valid d (l ++ m ++ [d]) [] r ((ofList m) :: acc)
    · simp only [Pos.Raw.unoffsetBy_zero]
      rw [show (Pos.Raw.next (ofList (l ++ (m ++ d :: r))) ⟨utf8Len l + utf8Len m⟩) =
          ⟨utf8Len l + utf8Len m + d.utf8Size⟩ by
        simpa [-ofList_append] using next_of_valid (l ++ m) d r]
      have hdc : ¬ (d == c) = true := h
      simpa [List.splitOnPPrepend_cons_eq_ite, hdc, Nat.add_assoc] using
        splitOnAux_of_valid c l (m ++ [d]) r acc
termination_by r.length

theorem splitOn_ofList (cs : List Char) (c : Char) :
    (ofList cs).splitOn (singleton c) = (cs.splitOn c).map ofList := by
  have hne : (singleton c == "") = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← toList_inj]
    simp
  simp only [splitOn, hne, Bool.false_eq_true, ↓reduceIte, List.splitOn_eq_splitOnP]
  simpa using splitOnAux_of_valid c [] [] cs []

@[expose] def decVal (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

theorem forIn_yield {α β : Type} (l : List α) (f : α → β → Id (ForInStep β)) (y : β)
    (hf : ∀ c ∈ l, ∀ x, f c x = ForInStep.yield y) (b : β) :
    forIn l b f = if l = [] then b else y := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf a (by simp)]
    change forIn l y f = _
    rw [ih (fun c hc => hf c (by simp [hc]))]
    simp

theorem foldl_congr {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ n, f n x = g n x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a (by simp)]
    exact foldl_congr f g l _ fun x hx => h x (by simp [hx])

theorem ne_underscore {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

theorem toNat!_ofList {ds : List Char} (hne : ds ≠ []) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (ofList ds).toNat! = decVal ds := by
  simp only [String.toNat!, Slice.toNat!, Slice.isNat]
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, copy_toSlice, toList_ofList]
  rw [forIn_yield (y := ((none : Option Bool), true)) ds]
  · simp only [hne, ↓reduceIte]
    split
    · exact foldl_congr _ _ ds 0 fun x hx n => by simp [ne_underscore (hd x hx)]
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [ne_underscore (hd c hc), hd c hc]
    rfl

end CFSG.KC.Str

end
