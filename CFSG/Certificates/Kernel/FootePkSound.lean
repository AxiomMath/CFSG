module

public import Certificates.Data.Kernel.FootePk
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.Certificates.Kernel.FootePk

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK CFSG.ComponentClassification.FooteSmall
  CFSG.Sporadic.Schreier

variable {n : Nat}

theorem decide_eq_eqV (a b : VP n) : decide (pkp a = pkp b) = eqV a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eqV, List.all_eq_true]
  simp only [List.mem_range, beq_iff_eq, Equiv.ext_iff, Fin.ext_iff, pkp_apply]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

theorem pkp_powV (a : VP n) : ∀ k, pkp (powV a k) = pkp a ^ k
  | 0 => by rw [powV, pkp_oneV, pow_zero]
  | k + 1 => by rw [powV, pkp_mulV, pkp_powV a k, pow_succ]

theorem key_pkp (k : Nat) (g : VP n) : key k (pkp g) = keyV k g := rfl

theorem commB_pkp (c t : VP n) : commB (pkp c) (tab (pkp t)) = commBV c t := by
  rw [tab_eq, Bool.eq_iff_iff, commB, commBV, List.all_eq_true, List.all_eq_true]
  simp only [List.mem_finRange, List.mem_range, decide_eq_true_eq, beq_iff_eq, Fin.ext_iff,
    pkp_apply, true_implies]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.2⟩

theorem dihB_pkp (u v : VP n) : dihB (pkp u) (pkp v) = dihBV u v := by
  have e1 : decide (pkp u * pkp u = 1) = eqV (mulV u u) (oneV n) := by
    rw [← decide_eq_eqV, pkp_mulV, pkp_oneV]
  have e2 : decide (pkp v * pkp v = 1) = eqV (mulV v v) (oneV n) := by
    rw [← decide_eq_eqV, pkp_mulV, pkp_oneV]
  have e3 : decide (pkp u * pkp v = pkp v * pkp u) = eqV (mulV u v) (mulV v u) := by
    rw [← decide_eq_eqV, pkp_mulV, pkp_mulV]
  have e4 : decide ((pkp u * pkp v) ^ 4 = 1) = eqV (powV (mulV u v) 4) (oneV n) := by
    rw [← decide_eq_eqV, pkp_powV, pkp_mulV, pkp_oneV]
  rw [dihB, dihBV, e1, e2, e3, e4]

theorem dihInvs_pkp (u v : VP n) : dihInvs (pkp u) (pkp v) = (dihInvsV u v).map pkp := by
  simp [dihInvs, dihInvsV, pkp_mulV, pkp_powV]

theorem spread_map {α β : Type*} (f : α → β) (m : Nat) (L : List α) :
    spread m (L.map f) = (spread m L).map f := by
  rw [spread, spread, List.map_filterMap, List.length_map]
  congr 1
  funext j
  rw [List.getElem?_map]

theorem fold_lt (d : Nat → Nat) (hd : ∀ i, d i < n) :
    ∀ k, Nat.fold k (fun i _ acc => acc * n + d i) 0 < n ^ k
  | 0 => by rw [Nat.fold_zero, pow_zero]; exact Nat.one_pos
  | k + 1 => by
    rw [Nat.fold_succ, pow_succ]
    have ih := fold_lt d hd k
    have h := hd k
    have : Nat.fold k (fun i _ acc => acc * n + d i) 0 * n + n ≤ n ^ k * n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right n ih
    omega

theorem keyV_lt (hn : 0 < n) (k : Nat) (g : VP n) : keyV k g < n ^ k :=
  fold_lt (fun i => if _ : i < n then fd (wd n) g.1.1 i else 0)
    (fun i => by
      by_cases h : i < n
      · rw [dif_pos h]; exact (g.2 i h).1
      · rw [dif_neg h]; exact hn) k

@[expose] def Marks (N : Nat) (seen : Array Bool) (S : Nat) : Prop :=
  seen.size = N ∧ ∀ i < N, seen[i]! = S.testBit i

theorem Marks.get {N : Nat} {seen : Array Bool} {S : Nat} (h : Marks N seen S) {i : Nat}
    (hi : i < N) : seen[i]! = S.testBit i := h.2 i hi

theorem Marks.set {N : Nat} {seen : Array Bool} {S : Nat} (h : Marks N seen S) {i : Nat}
    (hi : i < N) : Marks N (seen.set! i true) (S ||| 1 <<< i) := by
  refine ⟨by rw [Array.size_set!]; exact h.1, fun j hj => ?_⟩
  have hj' : j < seen.size := h.1 ▸ hj
  have hi' : i < seen.size := h.1 ▸ hi
  have hs : j < (seen.setIfInBounds i true).size := by simpa using hj'
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ← h.2 j hj,
    Array.set!_eq_setIfInBounds, getElem!_pos (seen.setIfInBounds i true) j hs,
    getElem!_pos seen j hj', Array.getElem_setIfInBounds hj']
  by_cases e : i = j
  · subst e
    simp
  · simp [e]

theorem Marks.init (N i : Nat) (hi : i < N) :
    Marks N ((Array.replicate N false).set! i true) (1 <<< i) := by
  have h0 : Marks N (Array.replicate N false) 0 :=
    ⟨by simp, fun j hj => by rw [getElem!_pos _ j (by simpa using hj)]; simp⟩
  have := h0.set hi
  rwa [Nat.zero_or] at this

variable (hn : 0 < n) {k : Nat}
include hn

theorem visit_eq (C : List (VP n)) (x : VP n) :
    ∀ (seen : Array Bool) (S : Nat) (F : List (VP n)), Marks (n ^ k) seen S →
      Marks (n ^ k) (visit k (C.map pkp) (seen, F.map pkp) (pkp x)).1
          (visitV k C (S, F) x).1 ∧
        (visit k (C.map pkp) (seen, F.map pkp) (pkp x)).2 = (visitV k C (S, F) x).2.map pkp := by
  induction C with
  | nil => intro seen S F h; exact ⟨h, rfl⟩
  | cons c C ih =>
    intro seen S F h
    have hk : key k (pkp x * pkp c) = keyV k (mulV x c) := by rw [← pkp_mulV, key_pkp]
    have hlt := keyV_lt hn k (mulV x c)
    simp only [visit, visitV, List.map_cons, List.foldl_cons] at ih ⊢
    rw [hk, h.get hlt]
    by_cases hb : S.testBit (keyV k (mulV x c)) = true
    · simp only [hb, if_true]
      exact ih seen S F h
    · simp only [hb, Bool.false_eq_true, if_false]
      have e : tab (pkp x * pkp c) :: F.map pkp = (mulV x c :: F).map pkp := by
        rw [tab_eq, List.map_cons, pkp_mulV]
      rw [e]
      exact ih _ _ _ (h.set hlt)

theorem frontier_eq (C : List (VP n)) :
    ∀ (Fr : List (VP n)) (seen : Array Bool) (S : Nat) (A : List (VP n)),
      Marks (n ^ k) seen S →
      Marks (n ^ k) ((Fr.map pkp).foldl (visit k (C.map pkp)) (seen, A.map pkp)).1
          (Fr.foldl (visitV k C) (S, A)).1 ∧
        ((Fr.map pkp).foldl (visit k (C.map pkp)) (seen, A.map pkp)).2 =
          (Fr.foldl (visitV k C) (S, A)).2.map pkp := by
  intro Fr
  induction Fr with
  | nil => intro seen S A h; exact ⟨h, rfl⟩
  | cons x Fr ih =>
    intro seen S A h
    simp only [List.map_cons, List.foldl_cons]
    obtain ⟨h1, h2⟩ := visit_eq hn C x seen S A h
    have e : visit k (C.map pkp) (seen, A.map pkp) (pkp x) =
        ((visit k (C.map pkp) (seen, A.map pkp) (pkp x)).1, (visitV k C (S, A) x).2.map pkp) := by
      rw [← h2]
    rw [e]
    exact ih _ _ _ h1

theorem search_eq (C : List (VP n)) :
    ∀ (fuel : Nat) (seen : Array Bool) (S : Nat) (F A : List (VP n)), Marks (n ^ k) seen S →
      search k (C.map pkp) fuel seen (F.map pkp) (A.map pkp) =
        (searchV k C fuel S F A).map pkp := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; rfl
  | succ fuel ih =>
    intro seen S F A h
    obtain ⟨h1, h2⟩ := frontier_eq hn C F seen S [] h
    rw [List.map_nil] at h1 h2
    rcases hres : F.foldl (visitV k C) (S, []) with ⟨S', found⟩
    rcases hres' : (F.map pkp).foldl (visit k (C.map pkp)) (seen, []) with ⟨seen', found'⟩
    rw [hres, hres'] at h1 h2
    simp only at h1 h2
    subst h2
    cases found with
    | nil => simp [search, searchV, hres, hres']
    | cons y found =>
      simp only [search, searchV, hres, hres', List.map_cons]
      rw [← List.map_cons, ← List.map_append]
      exact ih _ _ _ _ h1

theorem genCheck_eq (C T : List (VP n)) :
    genCheck k (C.map pkp) (T.map pkp) = genCheckV k C T := by
  have hm := Marks.init (n ^ k) (keyV k (oneV n)) (keyV_lt hn k (oneV n))
  have e1 : key k (1 : Equiv.Perm (Fin n)) = keyV k (oneV n) := by rw [← pkp_oneV, key_pkp]
  have e2 : ([1] : List (Equiv.Perm (Fin n))) = [oneV n].map pkp := by rw [List.map_cons,
    List.map_nil, pkp_oneV]
  rw [genCheck, genCheckV, e1, e2, search_eq hn C 64 _ _ _ _ hm, List.all_map]
  congr 1
  funext g
  simp only [Function.comp, List.contains_eq_any_beq, List.any_map]
  congr 1
  funext x
  exact decide_eq_eqV g x

theorem pairCheck_eq (m : Nat) (Q LP T : List (VP n)) :
    pairCheck k m (Q.map pkp) (LP.map pkp) (T.map pkp) = pairCheckV k m Q LP T := by
  rw [pairCheck, pairCheckV, List.all_map]
  congr 1
  funext u
  rw [Function.comp, List.all_map]
  congr 1
  funext v
  rw [Function.comp, dihB_pkp, dihInvs_pkp, List.flatMap_map]
  congr 1
  have e : ∀ t : VP n, ((LP.map pkp).filter fun c => commB c (tab (pkp t))) =
      (LP.filter fun c => commBV c t).map pkp := by
    intro t
    rw [List.filter_map]
    congr 1
    congr 1
    funext c
    exact commB_pkp c t
  simp only [Function.comp, e, spread_map]
  rw [← List.map_flatMap, genCheck_eq hn]

theorem pairCheck_of (m : Nat) (Q T : List (Equiv.Perm (Fin n))) (LP : List (VP n))
    (h : pairCheckV k m (Q.map codeV) LP (T.map codeV) = true) :
    pairCheck k m Q (LP.map pkp) T = true := by
  have e : ∀ L : List (Equiv.Perm (Fin n)), (L.map codeV).map pkp = L := fun L => by
    simp [List.map_map, Function.comp_def, pkp_codeV]
  rw [← e Q, ← e T, pairCheck_eq hn]
  exact h

end CFSG.Certificates.Kernel.FootePk

end
