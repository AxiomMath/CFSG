module

public import Init
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Basic

public section

namespace CFSG.KC.StrReplace

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model

theorem singleton_ne (c : Char) : String.singleton c ≠ "" := by
  intro h
  have := congrArg String.toList h
  simp at this

theorem singleton_append_ne (c : Char) (t : String) : String.singleton c ++ t ≠ "" := by
  intro h
  have := congrArg String.toList h
  simp at this

theorem fold_valid (c : Char) {s : Slice} (f : String → SearchStep s → String)
    (hm : ∀ a b sofar, (f sofar (.matched a b)).toList = sofar.toList)
    (hr : ∀ a b sofar, a ≤ b → ∀ h : a ≤ b,
      (f sofar (.rejected a b)).toList = sofar.toList ++ (s.slice a b h).copy.toList) :
    ∀ (pos : s.Pos) (l : List (SearchStep s)), IsValidSearchFrom (String.singleton c) pos l →
      ∀ t₁ t₂ init, pos.Splits t₁ t₂ →
        (l.foldl f init).toList = init.toList ++ t₂.toList.filter (· != c) := by
  intro pos l hv
  induction hv with
  | endPos =>
    intro t₁ t₂ init hs
    have h2 : t₂ = "" := (hs.eq_endPos_iff).1 rfl
    subst h2
    simp
  | @matched l start stop hm' hv ih =>
    intro t₁ t₂ init hs
    obtain ⟨u₁, u₂, h1, h2⟩ :=
      (ForwardStringSearcher.isLongestMatchAt_iff_splits (pat := String.singleton c)).1 hm'
    obtain ⟨-, e2⟩ := hs.eq h1
    rw [List.foldl_cons, ih (u₁ ++ String.singleton c) u₂ _ h2, hm, e2]
    simp
  | @mismatched l start stop hlt hno hv ih =>
    intro t₁ t₂ init hs
    have hs' := Slice.Pos.splits stop
    obtain ⟨t₅, hne, e1, e2⟩ := (hs.lt_iff_exists_eq_append hs').1 hlt
    have hle : start ≤ stop := Std.le_of_lt hlt
    have hcopy : (s.slice start stop hle).copy = t₅ := by
      obtain ⟨h, e⟩ := (Slice.copy_slice_eq_iff_splits (t := t₅)).2
        ⟨t₁, (s.sliceFrom stop).copy, by rw [← e2]; exact hs, by rw [← e1]; exact hs'⟩
      exact e
    have hnl : c ∉ t₅.toList := by
      intro hmem
      obtain ⟨a, b, hab⟩ := List.append_of_mem hmem
      have ht5 : t₅ = String.ofList a ++ (String.singleton c ++ String.ofList b) := by
        apply String.toList_injective
        rw [hab, String.toList_append, String.toList_append, String.toList_ofList,
          String.toList_singleton]
        simp
      have hsc : s.copy = (t₁ ++ String.ofList a) ++ (String.singleton c ++ (String.ofList b ++
          (s.sliceFrom stop).copy)) := by
        rw [hs.eq_append, e2, ht5]
        simp only [String.append_assoc]
      let q := Slice.Pos.ofEqAppend hsc
      have hq := Slice.Pos.splits_ofEqAppend hsc
      have hmq : MatchesAt (String.singleton c) q := by
        rw [ForwardStringSearcher.matchesAt_iff_toSlice, ForwardSliceSearcher.matchesAt_iff_splits]
        refine ⟨t₁ ++ String.ofList a, String.ofList b ++ (s.sliceFrom stop).copy, ?_⟩
        rw [copy_toSlice]
        exact hq
      have h1 : start ≤ q := (hs.le_iff_exists_eq_append hq).2
        ⟨String.ofList a, rfl, by rw [e2, ht5]; simp only [String.append_assoc]⟩
      have h2 : q < stop := (hq.lt_iff_exists_eq_append hs').2
        ⟨String.singleton c ++ String.ofList b, singleton_append_ne c _,
          by rw [e1, ht5]; simp only [String.append_assoc], by simp only [String.append_assoc]⟩
      exact hno q h1 h2 hmq
    rw [List.foldl_cons, ih _ _ _ hs', hr start stop init hle hle, hcopy, e2,
      String.toList_append, List.filter_append, List.append_assoc]
    congr 2
    refine (List.filter_eq_self.2 fun x hx => ?_).symm
    have : x ≠ c := fun h => hnl (h ▸ hx)
    simpa using this

theorem replace_char (c : Char) (s : String) :
    (s.replace (String.singleton c) "").toList = s.toList.filter (· != c) := by
  unfold String.replace String.Slice.replace
  rw [← Std.Iter.foldl_toList]
  have hv := (ForwardStringSearcher.lawfulToForwardSearcherModel (pat := String.singleton c)
    (singleton_ne c)).isValidSearchFrom_toList s.toSlice
  rw [fold_valid c _ (fun _ _ _ => by simp; exact isEmpty_toSlice_iff.2 rfl)
    (fun a b sofar _ h => by simp [Slice.slice!, h])
    _ _ hv "" s.toSlice.copy "" (Slice.splits_startPos s.toSlice), copy_toSlice]
  simp

theorem replace_char_ofList (c : Char) (l : List Char) :
    (String.ofList l).replace (String.singleton c) "" = String.ofList (l.filter (· != c)) := by
  apply String.toList_injective
  rw [replace_char, String.toList_ofList, String.toList_ofList]

end CFSG.KC.StrReplace

end
