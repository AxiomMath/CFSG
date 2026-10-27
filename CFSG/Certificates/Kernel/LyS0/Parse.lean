module

public import Certificates.Data.Kernel.LyS0.Check
public import CFSG.Certificates.Kernel.Common.StrSplit
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Basic

public section

namespace CFSG.KS.LyS0Parse

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model CFSG.KD.LyS0

theorem fold_valid {s : Slice} (f : String → SearchStep s → String)
    (hm : ∀ a b sofar, (f sofar (.matched a b)).toList = sofar.toList ++ [' '])
    (hr : ∀ a b sofar, a ≤ b → ∀ h : a ≤ b,
      (f sofar (.rejected a b)).toList = sofar.toList ++ (s.slice a b h).copy.toList) :
    ∀ (pos : s.Pos) (l : List (SearchStep s)), IsValidSearchFrom ("\n" : String) pos l →
      ∀ t₁ t₂ init, pos.Splits t₁ t₂ →
        (l.foldl f init).toList = init.toList ++ t₂.toList.map nlSp := by
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
    have hn : ("\n" : String).toList = ['\n'] := rfl
    simp [nlSp, hn]
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
      String.toList_append, List.map_append, List.append_assoc]
    congr 2
    have h5 : t₅.toList.map nlSp = t₅.toList := by
      rw [List.map_congr_left (g := fun c => c) (fun c hc => ?_), List.map_id']
      have : c ≠ '\n' := fun h => hnl (h ▸ hc)
      simp [nlSp, this]
    exact h5.symm

theorem replace_nl_sp (s : String) :
    (s.replace "\n" " ").toList = s.toList.map nlSp := by
  unfold String.replace String.Slice.replace
  rw [← Std.Iter.foldl_toList]
  have hv := (ForwardStringSearcher.lawfulToForwardSearcherModel (pat := "\n")
    (by decide)).isValidSearchFrom_toList s.toSlice
  rw [fold_valid _ (fun _ _ _ => by simp; rfl) (fun a b sofar _ h => by simp [Slice.slice!, h])
    _ _ hv "" s.toSlice.copy "" (Slice.splits_startPos s.toSlice), copy_toSlice]
  simp

theorem splitSp_eq (c : Char) : ∀ (l acc : List Char),
    splitSp c l acc = List.splitOnPPrepend (· == c) l acc
  | [], _ => by simp [splitSp]
  | x :: xs, acc => by
    unfold splitSp
    rw [List.splitOnPPrepend_cons_eq_ite]
    split
    · rw [splitSp_eq, List.splitOnPPrepend_nil_right]
    · rw [splitSp_eq]

theorem splitSp_nil (c : Char) (l : List Char) : splitSp c l [] = l.splitOn c := by
  rw [splitSp_eq, List.splitOn_eq_splitOnP, List.splitOnPPrepend_nil_right]

theorem space_eq : (" " : String) = String.singleton ' ' := by decide

theorem isEmpty_ofList (l : List Char) : (String.ofList l).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have : String.ofList (x :: xs) ≠ "" := by
      intro h
      have := congrArg String.toList h
      simp at this
    simp [String.isEmpty_iff, this]

theorem mem_splitSp {c : Char} : ∀ (l acc : List Char), (∀ x ∈ acc, x ≠ c) →
    ∀ p ∈ splitSp c l acc, ∀ x ∈ p, x ≠ c ∧ (x ∈ l ∨ x ∈ acc)
  | [], acc, hacc, p, hp, x, hx => by
    simp only [splitSp, List.mem_singleton] at hp
    subst hp
    have hx' : x ∈ acc := List.mem_reverse.1 hx
    exact ⟨hacc x hx', Or.inr hx'⟩
  | y :: ys, acc, hacc, p, hp, x, hx => by
    unfold splitSp at hp
    split at hp
    · rcases List.mem_cons.1 hp with rfl | hp'
      · have hx' : x ∈ acc := List.mem_reverse.1 hx
        exact ⟨hacc x hx', Or.inr hx'⟩
      · obtain ⟨h1, h2⟩ := mem_splitSp ys [] (by simp) p hp' x hx
        refine ⟨h1, Or.inl ?_⟩
        rcases h2 with h2 | h2
        · exact List.mem_cons_of_mem y h2
        · simp at h2
    · rename_i hyc
      have hy : y ≠ c := fun e => hyc (by rw [e]; exact beq_self_eq_true c)
      obtain ⟨h1, h2⟩ := mem_splitSp ys (y :: acc)
        (fun z hz => by
          rcases List.mem_cons.1 hz with rfl | hz'
          · exact hy
          · exact hacc z hz') p hp x hx
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl (List.mem_cons_of_mem y h2)
      · rcases List.mem_cons.1 h2 with rfl | h2'
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h2'

theorem parse_ofList {cs : List Char} (h : textOK cs = true) :
    ((((String.ofList cs).replace "\n" " ").splitOn " ").filter fun t => !t.isEmpty).toArray.map
      String.toNat! = (natsL cs).toArray := by
  have hr : (String.ofList cs).replace "\n" " " = String.ofList (cs.map nlSp) := by
    apply String.toList_injective
    rw [replace_nl_sp, String.toList_ofList, String.toList_ofList]
  rw [hr, space_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map, List.map_toArray]
  unfold natsL
  rw [splitSp_nil]
  congr 1
  rw [List.map_map]
  have e : ((fun t : String => !t.isEmpty) ∘ String.ofList) = fun l => !l.isEmpty := by
    funext l
    simp [isEmpty_ofList]
  rw [e]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
  have hne : p ≠ [] := by simpa using hp2
  have hdig : ∀ x ∈ p, x.isDigit = true := by
    intro x hx
    rw [← splitSp_nil] at hp1
    obtain ⟨hsp, hx'⟩ := mem_splitSp _ [] (by simp) p hp1 x hx
    have hx'' : x ∈ cs.map nlSp := by simpa using hx'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx''
    have hy' := List.all_eq_true.1 h y hy
    unfold nlSp at hsp ⊢
    by_cases hn : y = '\n'
    · simp [hn] at hsp
    · simp only [hn, ↓reduceIte] at hsp ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at hy'
      rcases hy' with (h1 | h1) | h1
      · exact h1
      · exact absurd h1 hsp
      · exact absurd h1 hn
  exact (CFSG.KC.Str.toNat!_ofList hne hdig).trans rfl

end CFSG.KS.LyS0Parse

end
