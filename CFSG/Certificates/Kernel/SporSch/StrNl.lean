module

public import Init
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Basic

public section

namespace CFSG.KS.SporSch.StrNl

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model

theorem fold_valid {s : Slice} (f : String → SearchStep s → String)
    (hm : ∀ a b sofar, (f sofar (.matched a b)).toList = sofar.toList)
    (hr : ∀ a b sofar, a ≤ b → ∀ h : a ≤ b,
      (f sofar (.rejected a b)).toList = sofar.toList ++ (s.slice a b h).copy.toList) :
    ∀ (pos : s.Pos) (l : List (SearchStep s)), IsValidSearchFrom ("\n" : String) pos l →
      ∀ t₁ t₂ init, pos.Splits t₁ t₂ →
        (l.foldl f init).toList = init.toList ++ t₂.toList.filter (· != '\n') := by
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
      (ForwardStringSearcher.isLongestMatchAt_iff_splits (pat := "\n")).1 hm'
    obtain ⟨-, e2⟩ := hs.eq h1
    rw [List.foldl_cons, ih (u₁ ++ "\n") u₂ _ h2, hm, e2]
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
    have hnl : '\n' ∉ t₅.toList := by
      intro hmem
      obtain ⟨a, b, hab⟩ := List.append_of_mem hmem
      have ht5 : t₅ = String.ofList a ++ ("\n" ++ String.ofList b) := by
        apply String.toList_injective
        have hn : ("\n" : String).toList = ['\n'] := rfl
        rw [hab, String.toList_append, String.toList_append, String.toList_ofList, hn]
        simp
      have hsc : s.copy = (t₁ ++ String.ofList a) ++ ("\n" ++ (String.ofList b ++
          (s.sliceFrom stop).copy)) := by
        rw [hs.eq_append, e2, ht5]
        simp only [String.append_assoc]
      let q := Slice.Pos.ofEqAppend hsc
      have hq := Slice.Pos.splits_ofEqAppend hsc
      have hmq : MatchesAt ("\n" : String) q := by
        rw [ForwardStringSearcher.matchesAt_iff_toSlice, ForwardSliceSearcher.matchesAt_iff_splits]
        refine ⟨t₁ ++ String.ofList a, String.ofList b ++ (s.sliceFrom stop).copy, ?_⟩
        rw [copy_toSlice]
        exact hq
      have h1 : start ≤ q := (hs.le_iff_exists_eq_append hq).2
        ⟨String.ofList a, rfl, by rw [e2, ht5]; simp only [String.append_assoc]⟩
      have h2 : q < stop := (hq.lt_iff_exists_eq_append hs').2
        ⟨"\n" ++ String.ofList b, by simp, by rw [e1, ht5]; simp only [String.append_assoc],
          rfl⟩
      exact hno q h1 h2 hmq
    rw [List.foldl_cons, ih _ _ _ hs', hr start stop init hle hle, hcopy, e2,
      String.toList_append, List.filter_append, List.append_assoc]
    congr 2
    refine (List.filter_eq_self.2 fun c hc => ?_).symm
    have : c ≠ '\n' := fun h => hnl (h ▸ hc)
    simpa using this

theorem replace_nl (s : String) : (s.replace "\n" "").toList = s.toList.filter (· != '\n') := by
  unfold String.replace String.Slice.replace
  rw [← Std.Iter.foldl_toList]
  have hv := (ForwardStringSearcher.lawfulToForwardSearcherModel (pat := "\n") (by decide)).isValidSearchFrom_toList s.toSlice
  rw [fold_valid _ (fun _ _ _ => by simp; exact isEmpty_toSlice_iff.2 rfl) (fun a b sofar _ h => by simp [Slice.slice!, h])
    _ _ hv "" s.toSlice.copy "" (Slice.splits_startPos s.toSlice), copy_toSlice]
  simp

end CFSG.KS.SporSch.StrNl

end
