module

public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.CFSGNative.AS91.M24Geom
public import Mathlib.Data.List.Sort

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem insN_eq (a : Nat) : ∀ l : List Nat, insN a l = l.orderedInsert (· ≤ ·) a
  | [] => (List.orderedInsert_nil _ _).symm
  | b :: l => by simp only [insN, List.orderedInsert_cons, insN_eq a l]

theorem sortN_eq : ∀ l : List Nat, sortN l = l.insertionSort (· ≤ ·)
  | [] => by simp [sortN]
  | b :: l => by simp only [sortN, List.insertionSort_cons, sortN_eq l, insN_eq]

theorem sortL_eq_sortN (l : List Nat) : Native.sortL l = sortN l := by
  rw [sortN_eq]
  exact List.mergeSort_eq_insertionSort (r := (· ≤ ·)) l

theorem toArray_getElem!_eq_getD {α : Type} [Inhabited α] (L : List α) (i : Nat) :
    L.toArray[i]! = L.getD i default := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem allIdx_iff {α : Type} [Inhabited α] (g : Nat → α → Bool) :
    ∀ (L : List α) (i : Nat), allIdx g L i = true ↔ ∀ p < L.length, g (i + p) (L.getD p default) = true
  | [], i => by simp [allIdx]
  | x :: L, i => by
    rw [allIdx, Bool.and_eq_true, allIdx_iff g L (i + 1)]
    constructor
    · rintro ⟨h0, h⟩ p hp
      cases p with
      | zero => simpa using h0
      | succ p =>
        have := h p (by simpa using hp)
        have e : i + 1 + p = i + (p + 1) := by omega
        rw [List.getD_cons_succ, ← e]
        exact this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun p hp => ?_⟩
      have := h (p + 1) (by simpa using hp)
      have e : i + 1 + p = i + (p + 1) := by omega
      rw [List.getD_cons_succ] at this
      rw [e]
      exact this

theorem range_all_iff (n : Nat) (f : Nat → Bool) :
    (List.range n).all f = true ↔ ∀ p < n, f p = true := by
  simp [List.all_eq_true, List.mem_range]

theorem range_all_eq_allIdx {α : Type} [Inhabited α] (L : List α) (g : Nat → α → Bool) :
    (List.range L.length).all (fun p => g p L.toArray[p]!) = allIdx g L 0 := by
  rw [Bool.eq_iff_iff, range_all_iff, allIdx_iff]
  simp only [toArray_getElem!_eq_getD, Nat.zero_add]

theorem ascL_pairwise : ∀ l : List Nat, ascL l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    rw [ascL, Bool.and_eq_true, decide_eq_true_iff] at h
    have hb := ascL_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) hb
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hb hc)

theorem ascL_nodup {l : List Nat} (h : ascL l = true) : l.Nodup :=
  (ascL_pairwise l h).imp Nat.ne_of_lt

theorem filter_range_perm {n : Nat} {p : Nat → Bool} {S : List Nat} (hS : S.Nodup)
    (hsub : ∀ x ∈ S, x < n) (hp : ∀ x < n, p x = true → x ∈ S) :
    ((List.range n).filter p).Perm (S.filter p) := by
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter p) (hS.filter p)).2 fun x => ?_
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hx, hpx⟩
    exact ⟨hp x hx hpx, hpx⟩
  · rintro ⟨hx, hpx⟩
    exact ⟨hsub x hx, hpx⟩

end CFSG.KC.M24G
