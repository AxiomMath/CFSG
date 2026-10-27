module

public import Certificates.Data.Kernel.Cert690.Base
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.C690

open CFSG.KC.Enum

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

@[expose] def IT.toList : IT → List (Nat × Nat)
  | .leaf => []
  | .node l k v r => l.toList ++ (k, v) :: r.toList

theorem IT.find_node (l : IT) (k v : Nat) (r : IT) (x d : Nat) :
    (IT.node l k v r).find x d =
      if x = k then v else if x < k then l.find x d else r.find x d := by
  show Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (r.find x d)
    (l.find x d) (Nat.blt x k)) v (Nat.beq x k) = _
  by_cases h1 : x = k
  · subst h1
    simp
  · have e1 : Nat.beq x k = false := by
      rw [Bool.eq_false_iff]
      intro h
      simp only [Nat.beq_eq] at h
      exact h1 h
    rw [e1, if_neg h1]
    by_cases h2 : x < k
    · have e2 : Nat.blt x k = true := by simpa using h2
      rw [e2, if_pos h2]
    · have e2 : Nat.blt x k = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        exact h2
      rw [e2, if_neg h2]

theorem lookup_cons' (k v x : Nat) (L : List (Nat × Nat)) :
    ((k, v) :: L).lookup x = if x = k then some v else L.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h
    simp
  · rw [beq_false_of_ne h, if_neg h]

theorem lookup_append_of_none {L M : List (Nat × Nat)} {x : Nat} (h : L.lookup x = none) :
    (L ++ M).lookup x = M.lookup x := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    obtain ⟨k, v⟩ := a
    rw [lookup_cons'] at h
    rw [List.cons_append, lookup_cons']
    by_cases hx : x = k
    · rw [if_pos hx] at h
      exact absurd h (by simp)
    · rw [if_neg hx] at h ⊢
      exact ih h

theorem lookup_append_of_some {L M : List (Nat × Nat)} {x v : Nat} (h : L.lookup x = some v) :
    (L ++ M).lookup x = some v := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons a L ih =>
    obtain ⟨k, w⟩ := a
    rw [lookup_cons'] at h
    rw [List.cons_append, lookup_cons']
    by_cases hx : x = k
    · rw [if_pos hx] at h ⊢
      exact h
    · rw [if_neg hx] at h ⊢
      exact ih h

theorem lookup_none {L : List (Nat × Nat)} {x : Nat} (h : ∀ a ∈ L, a.1 ≠ x) :
    L.lookup x = none := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    obtain ⟨k, w⟩ := a
    have hk : x ≠ k := fun e => h _ List.mem_cons_self e.symm
    rw [lookup_cons', if_neg hk]
    exact ih fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem mem_of_lookup {L : List (Nat × Nat)} {x v : Nat} (h : L.lookup x = some v) :
    (x, v) ∈ L := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons a L ih =>
    obtain ⟨k, w⟩ := a
    rw [lookup_cons'] at h
    by_cases hx : x = k
    · rw [if_pos hx] at h
      cases h
      subst hx
      exact List.mem_cons_self
    · rw [if_neg hx] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem find_eq_lookup : ∀ (t : IT), t.toList.Pairwise (fun a b => a.1 < b.1) →
    ∀ x d, t.find x d = (t.toList.lookup x).getD d
  | .leaf, _, x, d => rfl
  | .node l k v r, h, x, d => by
    have h' := h
    simp only [IT.toList, List.pairwise_append, List.pairwise_cons, List.mem_cons] at h'
    obtain ⟨hl, ⟨hk, hr⟩, hlr⟩ := h'
    have hlk : ∀ a ∈ l.toList, a.1 < k := fun a ha => hlr a ha (k, v) (Or.inl rfl)
    rw [IT.find_node]
    simp only [IT.toList]
    by_cases h1 : x = k
    · subst h1
      rw [if_pos rfl, lookup_append_of_none (lookup_none fun a ha => (hlk a ha).ne),
        lookup_cons', if_pos rfl]
      rfl
    · rw [if_neg h1]
      by_cases h2 : x < k
      · rw [if_pos h2, find_eq_lookup l hl x d]
        cases e : l.toList.lookup x with
        | some w => rw [lookup_append_of_some e]
        | none =>
          rw [lookup_append_of_none e]
          have : ((k, v) :: r.toList).lookup x = none :=
            lookup_none fun a ha => by
              rcases List.mem_cons.1 ha with rfl | ha
              · exact Ne.symm h1
              · exact (lt_trans h2 (hk a ha)).ne'
          rw [this]
      · rw [if_neg h2, find_eq_lookup r hr x d,
          lookup_append_of_none (lookup_none fun a ha => by
            have := hlk a ha
            omega), lookup_cons', if_neg h1]

theorem bt_zero (xs : List (Nat × Nat)) : bt 0 xs = (IT.leaf, xs) := rfl

theorem bt_succ (dp : Nat) (xs : List (Nat × Nat)) :
    bt (dp + 1) xs = match (bt dp xs).2 with
      | [] => ((bt dp xs).1, [])
      | kv :: rest => (IT.node (bt dp xs).1 kv.1 kv.2 (bt dp rest).1, (bt dp rest).2) := by
  show (fun p => List.rec (motive := fun _ => IT × List (Nat × Nat)) (p.1, [])
        (fun kv rest _ => (fun q => (IT.node p.1 kv.1 kv.2 q.1, q.2)) (bt dp rest)) p.2)
      (bt dp xs) = _
  simp only
  cases (bt dp xs).2 <;> rfl

theorem bt_append : ∀ (dp : Nat) (xs : List (Nat × Nat)),
    (bt dp xs).1.toList ++ (bt dp xs).2 = xs
  | 0, xs => rfl
  | dp + 1, xs => by
    have ih := bt_append dp xs
    rw [bt_succ]
    revert ih
    cases (bt dp xs).2 with
    | nil => intro ih; simpa using ih
    | cons kv rest =>
      intro ih
      simp only [IT.toList]
      rw [List.append_assoc, List.cons_append, bt_append dp rest]
      exact ih

theorem bt_length : ∀ (dp : Nat) (xs : List (Nat × Nat)),
    (bt dp xs).1.toList.length = min xs.length (2 ^ dp - 1)
  | 0, xs => by simp [bt_zero, IT.toList]
  | dp + 1, xs => by
    have ih := bt_length dp xs
    have ha := congrArg List.length (bt_append dp xs)
    rw [List.length_append] at ha
    have hp : 2 ^ (dp + 1) = 2 * 2 ^ dp := by rw [Nat.pow_succ]; ring
    have h1 : 1 ≤ 2 ^ dp := Nat.one_le_two_pow
    rw [bt_succ]
    revert ih ha
    cases (bt dp xs).2 with
    | nil =>
      intro ih ha
      simp only [List.length_nil, Nat.add_zero] at ha ⊢
      rw [ih] at ha ⊢
      omega
    | cons kv rest =>
      intro ih ha
      simp only [IT.toList, List.length_append, List.length_cons] at ha ⊢
      have ih2 := bt_length dp rest
      rw [ih, ih2]
      rw [ih] at ha
      omega

theorem bt_rest_nil {dp : Nat} {xs : List (Nat × Nat)} (h : xs.length ≤ 2 ^ dp - 1) :
    (bt dp xs).2 = [] := by
  have ha := congrArg List.length (bt_append dp xs)
  rw [List.length_append, bt_length] at ha
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem bt_toList {dp : Nat} {xs : List (Nat × Nat)} (h : xs.length ≤ 2 ^ dp - 1) :
    (bt dp xs).1.toList = xs := by
  have := bt_append dp xs
  rwa [bt_rest_nil h, List.append_nil] at this

theorem find_idxT {l : List (Nat × Nat)} (hl : l.length ≤ 65535)
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (x d : Nat) :
    (idxT l).find x d = (l.lookup x).getD d := by
  have e : (bt 16 l).1.toList = l := bt_toList (by norm_num; omega)
  show (bt 16 l).1.find x d = _
  rw [find_eq_lookup _ (by rw [e]; exact hs), e]

theorem posPairs_cons (x : Nat) (E : List Nat) (s : Nat) :
    posPairs (x :: E) s = (s, x) :: posPairs E (s + 1) := rfl

theorem posPairs_length (E : List Nat) : ∀ s, (posPairs E s).length = E.length := by
  induction E with
  | nil => intro s; rfl
  | cons x E ih => intro s; simp [posPairs_cons, ih]

theorem posPairs_fst (E : List Nat) : ∀ s, ∀ a ∈ posPairs E s, s ≤ a.1 := by
  induction E with
  | nil => intro s a ha; simp [posPairs] at ha
  | cons x E ih =>
    intro s a ha
    rw [posPairs_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact le_rfl
    · exact le_trans (Nat.le_succ s) (ih (s + 1) a ha)

theorem posPairs_sorted (E : List Nat) :
    ∀ s, (posPairs E s).Pairwise (fun a b => a.1 < b.1) := by
  induction E with
  | nil => intro s; exact List.Pairwise.nil
  | cons x E ih =>
    intro s
    rw [posPairs_cons, List.pairwise_cons]
    exact ⟨fun a ha => Nat.lt_of_lt_of_le (Nat.lt_succ_self s) (posPairs_fst E (s + 1) a ha),
      ih (s + 1)⟩

theorem posPairs_lookup (E : List Nat) : ∀ s i, (posPairs E s).lookup (s + i) = E[i]? := by
  induction E with
  | nil => intro s i; rfl
  | cons x E ih =>
    intro s i
    rw [posPairs_cons, lookup_cons']
    cases i with
    | zero => simp
    | succ i =>
      rw [if_neg (by omega), List.getElem?_cons_succ, show s + (i + 1) = (s + 1) + i by omega, ih]

theorem find_posT {E : List Nat} (hE : E.length ≤ 65535) (i d : Nat) :
    (posT E).find i d = E.getD i d := by
  unfold posT
  rw [find_idxT (by rw [posPairs_length]; exact hE) (posPairs_sorted E 0),
    show i = 0 + i by omega, posPairs_lookup, Nat.zero_add, List.getD_eq_getElem?_getD]

theorem sortedK_pairwise : ∀ (l : List (Nat × Nat)), sortedK l = true →
    l.Pairwise (fun a b => a.1 < b.1)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    have h' : (Nat.blt a.1 b.1 && sortedK (b :: rest)) = true := by
      rw [← bAnd_eq]
      exact h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    have ih := sortedK_pairwise (b :: rest) h'.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact lt_trans h'.1 (List.rel_of_pairwise_cons ih hx)

theorem ixAllK_cons (T : IT) (n x : Nat) (E : List Nat) (s : Nat) :
    ixAllK T n (x :: E) s = (Nat.beq (T.find x n) s && ixAllK T n E (s + 1)) := by
  show strictB s (fun i => Bool.rec (motive := fun _ => Bool) false (ixAllK T n E (Nat.succ i))
    (Nat.beq (T.find x n) i)) = _
  rw [strictB_eq, bAnd_eq]

theorem ixAllK_spec (T : IT) (n : Nat) (E : List Nat) :
    ∀ s, ixAllK T n E s = true → ∀ i (h : i < E.length), T.find E[i] n = s + i := by
  induction E with
  | nil => intro s _ i h; simp at h
  | cons x E ih =>
    intro s hs i hi
    rw [ixAllK_cons, Bool.and_eq_true, Nat.beq_eq] at hs
    cases i with
    | zero => simpa using hs.1
    | succ i =>
      have := ih (s + 1) hs.2 i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      rw [this]
      omega

theorem find_idxT_eq_idxOf {S : List (Nat × Nat)} {E : List Nat} (h : ixOK S E = true) :
    E.Nodup ∧ ∀ c, (idxT S).find c E.length = E.idxOf c := by
  unfold ixOK at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨⟨hs, hlen, hmax⟩, hall⟩ := h
  have hp := sortedK_pairwise S hs
  have hf : ∀ c, (idxT S).find c E.length = (S.lookup c).getD E.length :=
    fun c => find_idxT hmax hp c _
  have hpos := ixAllK_spec _ _ E 0 hall
  have hlk : ∀ i (hi : i < E.length), S.lookup E[i] = some i := by
    intro i hi
    have := hpos i hi
    rw [hf, Nat.zero_add] at this
    cases e : S.lookup E[i] with
    | none => rw [e] at this; simp at this; omega
    | some w => rw [e] at this; simpa using this
  have hnd : E.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b hab
    have h1 := hlk a a.isLt
    have h2 := hlk b b.isLt
    simp only [List.get_eq_getElem] at hab
    rw [hab, h2] at h1
    exact Fin.ext (Option.some_inj.1 h1).symm
  refine ⟨hnd, fun c => ?_⟩
  rw [hf]
  by_cases hc : c ∈ E
  · have hi := List.idxOf_lt_length_iff.2 hc
    have := hlk _ hi
    rw [List.getElem_idxOf] at this
    rw [this]
    rfl
  · rw [List.idxOf_eq_length hc]
    cases e : S.lookup c with
    | none => rfl
    | some v =>
      exfalso
      have hmem : (c, v) ∈ S := mem_of_lookup e
      let T := (List.finRange E.length).map fun i => (E.get i, (i : Nat))
      have hT : T ⊆ S := by
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
        rw [List.get_eq_getElem]
        exact mem_of_lookup (hlk i.1 i.2)
      have hTnd : T.Nodup := by
        refine List.Nodup.map (fun i j hij => Fin.ext ?_) (List.nodup_finRange _)
        exact (Prod.ext_iff.1 hij).2
      have hperm := (hTnd.subperm hT).perm_of_length_le (by simp [T, hlen])
      obtain ⟨i, _, hi⟩ := List.mem_map.1 (hperm.mem_iff.2 hmem)
      have e1 : E.get i = c := (Prod.ext_iff.1 hi).1
      exact hc (e1 ▸ List.get_mem E i)

end CFSG.KC.C690

end
