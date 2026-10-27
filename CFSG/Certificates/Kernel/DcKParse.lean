module

public import Certificates.Data.Kernel.DcK
public import CFSG.Certificates.Kernel.Common.StrSplit
import all Init.Data.String.Slice
import all Init.Data.String.Search

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative

theorem splitGo_eq (c : Char) : ∀ (l acc : List Char),
    splitGo c l acc = List.splitOnPPrepend (· == c) l acc
  | [], _ => by simp [splitGo]
  | x :: xs, acc => by
    unfold splitGo
    rw [List.splitOnPPrepend_cons_eq_ite]
    split
    · rw [splitGo_eq, List.splitOnPPrepend_nil_right]
    · rw [splitGo_eq]

theorem splitGo_nil (c : Char) (l : List Char) : splitGo c l [] = l.splitOn c := by
  rw [splitGo_eq, List.splitOn_eq_splitOnP, List.splitOnPPrepend_nil_right]

theorem comma_eq : ("," : String) = String.singleton ',' := by decide

theorem space_eq : (" " : String) = String.singleton ' ' := by decide

theorem ofList_ne_empty (l : List Char) :
    decide (String.ofList l ≠ "") = !l.isEmpty := by
  cases l with
  | nil => simp
  | cons x xs =>
    have : String.ofList (x :: xs) ≠ "" := by
      intro h
      have := congrArg String.toList h
      simp at this
    simp [this]

theorem digits_ofList (l : List Char) : digits (String.ofList l) = digitsK l := by
  simp [digits, digitsK]

theorem parseWords_ofList (cs : List Char) :
    parseWords (String.ofList cs) = (wordsK cs).toArray := by
  unfold parseWords wordsK
  rw [comma_eq, CFSG.KC.Str.splitOn_ofList, splitGo_nil, List.filter_map]
  have e : ((fun s : String => decide (s ≠ "")) ∘ String.ofList) = fun l => !l.isEmpty := by
    funext l
    exact ofList_ne_empty l
  rw [e, List.map_toArray, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => digits_ofList l

theorem isNum_spec {p : List Char} (h : isNum p = true) :
    p ≠ [] ∧ ∀ c ∈ p, c.isDigit = true := by
  unfold isNum at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
  exact h

theorem toNat?_num {p : List Char} (h : isNum p = true) :
    (String.ofList p).toNat? = some (decK p) := by
  obtain ⟨hne, hd⟩ := isNum_spec h
  open String in
  simp only [String.toNat?, Slice.toNat?, Slice.isNat]
  open String in
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, copy_toSlice, toList_ofList]
  rw [CFSG.KC.Str.forIn_yield (y := ((none : Option Bool), true)) p]
  · simp only [hne, ↓reduceIte]
    split
    · congr 1
      exact CFSG.KC.Str.foldl_congr _ _ p 0 fun x hx n => by
        simp [CFSG.KC.Str.ne_underscore (hd x hx)]
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [CFSG.KC.Str.ne_underscore (hd c hc), hd c hc]
    rfl

theorem numsK_spec : ∀ (ps : List (List Char)) (L : List Nat), numsK ps = some L →
    (ps.map String.ofList).filterMap String.toNat? = L
  | [], L, h => by
    simp only [numsK, Option.some.injEq] at h
    simp [← h]
  | p :: ps, L, h => by
    unfold numsK at h
    split at h
    · rename_i hp
      cases e : numsK ps with
      | none => rw [e] at h; simp at h
      | some L' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h, List.map_cons, List.filterMap_cons, toNat?_num hp, numsK_spec ps L' e]
    · simp at h

theorem parseNats_ofList {cs : List Char} {L : List Nat} (h : natsK cs = some L) :
    parseNats (String.ofList cs) = L.toArray := by
  unfold parseNats
  unfold natsK at h
  rw [space_eq, CFSG.KC.Str.splitOn_ofList, ← splitGo_nil, numsK_spec _ L h]

theorem toNat!_num {p : List Char} (h : isNum p = true) : (String.ofList p).toNat! = decK p := by
  obtain ⟨hne, hd⟩ := isNum_spec h
  rw [CFSG.KC.Str.toNat!_ofList hne hd]
  rfl

theorem edgeK_spec {e : List Char} {E : Nat × Nat × List Nat} (h : edgeK e = some E) :
    (match (String.ofList e).splitOn " " with
      | [a, b, w] => (a.toNat!, b.toNat!, digits w)
      | _ => (0, 0, [])) = E := by
  unfold edgeK at h
  rw [space_eq, CFSG.KC.Str.splitOn_ofList, ← splitGo_nil]
  split at h
  · rename_i a b w hs
    rw [hs]
    split at h
    · rename_i hab
      simp only [Bool.and_eq_true] at hab
      simp only [Option.some.injEq] at h
      simp only [List.map_cons, List.map_nil]
      rw [toNat!_num hab.1, toNat!_num hab.2, digits_ofList, h]
    · simp at h
  · simp at h

theorem edgesGo_spec : ∀ (ps : List (List Char)) (L : List (Nat × Nat × List Nat)),
    edgesGo ps = some L →
    (ps.map String.ofList).map (fun e => match e.splitOn " " with
      | [a, b, w] => (a.toNat!, b.toNat!, digits w)
      | _ => (0, 0, [])) = L
  | [], L, h => by
    simp only [edgesGo, Option.some.injEq] at h
    simp [← h]
  | p :: ps, L, h => by
    unfold edgesGo at h
    split at h
    · rename_i E hE
      cases e : edgesGo ps with
      | none => rw [e] at h; simp at h
      | some L' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h, List.map_cons, List.map_cons, edgeK_spec hE, edgesGo_spec ps L' e]
    · simp at h

theorem parseEdges_ofList {cs : List Char} {L : List (Nat × Nat × List Nat)}
    (h : edgesK cs = some L) : parseEdges (String.ofList cs) = L.toArray := by
  unfold parseEdges
  unfold edgesK at h
  rw [comma_eq, CFSG.KC.Str.splitOn_ofList, ← splitGo_nil, List.filter_map]
  have e : ((fun s : String => decide (s ≠ "")) ∘ String.ofList) = fun l => !l.isEmpty := by
    funext l
    exact ofList_ne_empty l
  rw [e, List.map_toArray]
  congr 1
  exact edgesGo_spec _ L h

end CFSG.KC.DcK

end
