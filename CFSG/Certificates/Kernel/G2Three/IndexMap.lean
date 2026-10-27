module

public import CFSG.Quasithin.Background.G2UClosure
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Data.HashMap.Lemmas
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.G2Three

open CFSG.Quasithin.G2U

theorem indexMap_prefix (es : Array (List ℕ)) :
    ∀ n, n ≤ es.size →
      (∀ y t, ((List.range n).foldl (fun m t => m.insert (es.getD t []) t)
          ({} : Std.HashMap (List ℕ) ℕ)).get? y = some t → t < n ∧ es.getD t [] = y) ∧
        ∀ t < n, (((List.range n).foldl (fun m t => m.insert (es.getD t []) t)
          ({} : Std.HashMap (List ℕ) ℕ)).get? (es.getD t [])).isSome
  | 0, _ => by
    refine ⟨fun y t h => ?_, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    simp [Std.HashMap.get?_eq_getElem?] at h
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := indexMap_prefix es n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun y t h => ?_, fun t ht => ?_⟩
    · rw [Std.HashMap.get?_insert] at h
      split_ifs at h with he
      · cases h
        exact ⟨by omega, beq_iff_eq.1 he⟩
      · obtain ⟨h1, h2⟩ := ih1 y t h
        exact ⟨by omega, h2⟩
    · rw [Std.HashMap.get?_insert]
      split_ifs with he
      · rfl
      · exact ih2 t (by
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
          · exact h
          · subst h
            exact absurd (beq_self_eq_true _) he)

theorem indexMap_get? {es : Array (List ℕ)} {y : List ℕ} {t : ℕ}
    (h : (indexMap es).get? y = some t) : t < es.size ∧ es.getD t [] = y :=
  (indexMap_prefix es es.size le_rfl).1 y t h

theorem indexMap_isSome {es : Array (List ℕ)} {t : ℕ} (ht : t < es.size) :
    ((indexMap es).get? (es.getD t [])).isSome :=
  (indexMap_prefix es es.size le_rfl).2 t ht

theorem found_indexMap {es : Array (List ℕ)} {y : List ℕ} :
    found es (indexMap es) y = true ↔ ∃ t < es.size, es.getD t [] = y := by
  unfold found
  constructor
  · intro h
    cases hm : (indexMap es).get? y with
    | none => rw [hm] at h; cases h
    | some t =>
      rw [hm] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨t, h.1, h.2⟩
  · rintro ⟨t, ht, rfl⟩
    have hs := indexMap_isSome ht
    cases hm : (indexMap es).get? (es.getD t []) with
    | none => rw [hm] at hs; cases hs
    | some s =>
      obtain ⟨h1, h2⟩ := indexMap_get? hm
      simp [h1, h2]

theorem all_range_of {n : ℕ} {f : ℕ → Bool} (h : ∀ t < n, f t = true) :
    (List.range n).all f = true := by
  rw [List.all_eq_true]
  intro t ht
  exact h t (List.mem_range.1 ht)

theorem closedCheck_of {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {es : Array (List ℕ)}
    (h : ∀ v < es.size, ∀ g ∈ gens, ∃ t < es.size, es.getD t [] = mul (es.getD v []) g) :
    closedCheck mul gens es = true := by
  unfold closedCheck
  refine all_range_of fun v hv => ?_
  rw [List.all_eq_true]
  intro g hg
  exact found_indexMap.2 (h v hv g hg)

theorem distinctCheck_of {es : Array (List ℕ)}
    (h : ∀ t < es.size, ∀ t' < es.size, es.getD t [] = es.getD t' [] → t = t') :
    distinctCheck es = true := by
  unfold distinctCheck
  refine all_range_of fun t ht => ?_
  have hs := indexMap_isSome ht
  cases hm : (indexMap es).get? (es.getD t []) with
  | none => rw [hm] at hs; cases hs
  | some s =>
    obtain ⟨h1, h2⟩ := indexMap_get? hm
    rw [h t ht s h1 h2.symm]
    exact beq_self_eq_true _

theorem allCheck_of {p : List ℕ → Bool} {es : Array (List ℕ)}
    (h : ∀ t < es.size, p (es.getD t []) = true) : allCheck p es = true := by
  unfold allCheck
  exact all_range_of h

end CFSG.KC.G2Three

end
