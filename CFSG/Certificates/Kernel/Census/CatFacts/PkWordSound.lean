module

public import Certificates.Data.Kernel.Census.CatFacts.PkWord
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CFSG.Certificates.Kernel.PkEnum

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.KS.PK CFSG.GH74.KGroups

theorem forceD_eq {β : Sort _} (y : Nat) (k : (p : Nat) → p = y → β) : forceD y k = k y rfl := by
  cases y <;> rfl

theorem forceV_eq {n : Nat} {β : Sort _} (a : VP n) (k : VP n → β) : forceV a k = k a := by
  unfold forceV
  rw [forceD_eq, forceD_eq]

theorem forceL_eq {n : Nat} {β : Sort _} (l : List (VP n)) (k : List (VP n) → β) :
    forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => rw [forceL, forceV_eq, ih]

theorem forceLL_eq {n : Nat} {β : Sort _} (L : List (List (VP n)))
    (k : List (List (VP n)) → β) : forceLL L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons l L ih => rw [forceLL, forceL_eq, ih]

theorem forceF_eq {n : Nat} {β : Sort _} (x : Fin n) (k : Fin n → β) : forceF x k = k x := by
  unfold forceF
  rw [forceD_eq]

theorem forceE_eq {n : Nat} {β : Sort _} (l : List (Fin n × VP n))
    (k : List (Fin n × VP n) → β) : forceE l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons e l ih => rw [forceE, forceF_eq, forceV_eq, ih]

theorem forceLv_eq {n : Nat} {β : Sort _} (L : List (Fin n × StV n))
    (k : List (Fin n × StV n) → β) : forceLv L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons e L ih => rw [forceLv, forceF_eq, forceE_eq, ih]

theorem pkpW_nil {n : Nat} : pkpW ([] : List (VP n)) = 1 := rfl

theorem pkpW_cons {n : Nat} (a : VP n) (w : List (VP n)) : pkpW (a :: w) = pkp a * pkpW w := by
  rw [pkpW, List.map_cons, List.prod_cons]
  rfl

theorem pkpW_append {n : Nat} (u v : List (VP n)) : pkpW (u ++ v) = pkpW u * pkpW v := by
  rw [pkpW, List.map_append, List.prod_append]
  rfl

theorem pkpW_invW {n : Nat} (w : List (VP n)) : pkpW (invW w) = (pkpW w)⁻¹ := by
  rw [pkpW, invW, pkpW, List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  rfl

theorem pkpW_single {n : Nat} (a : VP n) : pkpW [a] = pkp a := by
  rw [pkpW_cons, pkpW_nil, mul_one]

theorem imgW_eq {n : Nat} (w : List (VP n)) (i : Fin n) : imgW w i = (pkpW w i : Nat) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [pkpW_cons, Equiv.Perm.mul_apply, pkp_apply, ← ih]
    rfl

theorem range_all_iff {n : Nat} (p : Nat → Bool) :
    (List.range n).all p = true ↔ ∀ i : Fin n, p i = true := by
  rw [List.all_eq_true]
  simp only [List.mem_range]
  exact ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩

theorem isOneW_eq {n : Nat} (w : List (VP n)) : isOneW w = decide (pkpW w = 1) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, isOneW, range_all_iff]
  simp only [imgW_eq, beq_iff_eq]
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    rw [h]
    rfl

theorem eqW_eq {n : Nat} (u v : List (VP n)) : eqW u v = decide (pkpW u = pkpW v) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, eqW, range_all_iff]
  simp only [imgW_eq, beq_iff_eq]
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    rw [h]

theorem memW_eq {n : Nat} (u : List (VP n)) (L : List (List (VP n))) :
    memW u L = decide (pkpW u ∈ L.map pkpW) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, memW, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨b, hb, h⟩
    rw [eqW_eq, decide_eq_true_iff] at h
    exact ⟨b, hb, h.symm⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by rw [eqW_eq, decide_eq_true_iff, h]⟩

theorem lookupN_eq {n : Nat} {β : Type} (l : List (Fin n × β)) (x : Fin n) :
    lookupN l x.val = l.lookup x := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    rw [lookupN, List.lookup_cons, ih]
    by_cases h : x = a
    · subst h
      simp
    · have h1 : (a.val == x.val) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h2 => h (Fin.ext h2.symm)
      have h2 : (x == a) = false := beq_eq_false_iff_ne.2 h
      simp only [h1, h2]
      rfl

theorem siftW_eq {n : Nat} (levels : List (Fin n × StV n)) (w : List (VP n)) (v : VP n)
    (hv : pkp v = pkpW w) : siftW levels w = siftV levels v := by
  induction levels generalizing w v with
  | nil =>
    rw [siftW, siftV, siftResV, isOneW_eq]
    change decide (pkpW w = 1) = schreierPermEq (pkp v) 1
    rw [hv]
    exact (Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff, schreierPermEq_eq_true_iff])).symm
  | cons e levels ih =>
    obtain ⟨b, q⟩ := e
    have hb : imgW w b = (pkp v b : Nat) := by rw [imgW_eq, hv]
    have hs : siftV ((b, q) :: levels) v = match q.entries.lookup (pkp v b) with
        | none => false
        | some t => siftV levels (mulV (invV t) v) := by
      unfold siftV
      rw [siftResV]
      cases q.entries.lookup (pkp v b) <;> rfl
    rw [siftW, hb, lookupN_eq, hs]
    cases q.entries.lookup (pkp v b) with
    | none => rfl
    | some t =>
      exact ih _ _ (by rw [pkp_mulV, pkp_invV, pkpW_cons, hv, pkp_invV])

theorem sift_pkpW {n : Nat} (Q : RawSchreierDatum n) (w : List (VP n)) (i : Nat) :
    Q.sift (pkpW w) i = siftW (levelsV (strongV Q) Q.base i) w := by
  rw [sift_eq_siftP, siftP, siftW_eq _ w _ (pkp_codeV _)]

theorem sift_pkp {n : Nat} (Q : RawSchreierDatum n) (a : VP n) (i : Nat) :
    Q.sift (pkp a) i = siftW (levelsV (strongV Q) Q.base i) [a] := by
  rw [← sift_pkpW, pkpW_single]

theorem productsW_map {n : Nat} (Ts : List (List (VP n))) :
    (productsV Ts).map pkp = (productsW Ts).map pkpW := by
  induction Ts with
  | nil => simp [productsV, productsW, pkp_oneV, pkpW_nil]
  | cons T Ts ih =>
    simp only [productsV, productsW, List.map_flatMap, List.flatMap_map]
    congr 1
    funext t
    rw [List.map_map, List.map_map]
    have h : (pkp ∘ mulV t) = (pkp t * ·) ∘ pkp := by
      funext v
      simp [pkp_mulV]
    have h2 : (pkpW ∘ (t :: ·)) = (pkp t * ·) ∘ pkpW := by
      funext v
      simp [pkpW_cons]
    rw [h, h2, ← List.map_map, ih, List.map_map]

theorem elemsT_eq_W {n : Nat} (Q : RawSchreierDatum n) :
    elemsT Q = (productsW (transL Q)).map pkpW := by
  rw [elemsT_eq_elemsV, elemsV, enumV, productsW_map]
  rfl

theorem flatMap_eq_range' {α β : Type*} (l : List α) (d : α) (f : α → List β) :
    l.flatMap f = (List.range l.length).flatMap fun j => f (l.getD j d) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    rfl

theorem productsW_blocks {n : Nat} (Ts : List (List (VP n))) (h : Ts ≠ []) :
    productsW Ts = (List.range (Ts.headD []).length).flatMap (blockW Ts) := by
  obtain ⟨T, Ts', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [productsW, flatMap_eq_range' _ (oneV n)]
  rfl

theorem transL_ne_nil {n : Nat} (Q : RawSchreierDatum n) (hk : 1 ≤ Q.baseCount) :
    transL Q ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [transL, List.length_map, List.length_finRange, List.length_nil] at this
  omega

theorem elemsT_all_of_blocks {n : Nat} (Q : RawSchreierDatum n) (hk : 1 ≤ Q.baseCount)
    (p : Equiv.Perm (Fin n) → Bool)
    (h : ∀ j < ((transL Q).headD []).length, (blockW (transL Q) j).all (fun w => p (pkpW w)) = true) :
    (elemsT Q).all p = true := by
  rw [elemsT_eq_W, productsW_blocks _ (transL_ne_nil Q hk), List.all_map, List.all_flatMap,
    List.all_eq_true]
  intro j hj
  exact h j (List.mem_range.1 hj)

theorem elemsT_count_blocks {n : Nat} (Q : RawSchreierDatum n) (hk : 1 ≤ Q.baseCount)
    (p : Equiv.Perm (Fin n) → Bool) :
    ((elemsT Q).filter p).length = ((List.range ((transL Q).headD []).length).map fun j =>
      ((blockW (transL Q) j).filter fun w => p (pkpW w)).length).sum := by
  rw [elemsT_eq_W, productsW_blocks _ (transL_ne_nil Q hk), List.filter_map, List.length_map,
    List.filter_flatMap, List.length_flatMap]
  rfl

theorem pkp_getD_map {n : Nat} (S : List (Equiv.Perm (Fin n))) (k : Nat) :
    pkp ((S.map codeV).getD k (oneV n)) = S.getD k 1 := by
  induction S generalizing k with
  | nil => exact pkp_oneV n
  | cons s S ih =>
    cases k with
    | zero => exact pkp_codeV s
    | succ k => exact ih k

theorem pkpW_codesW {n : Nat} (S : List (Equiv.Perm (Fin n))) (w : List ℤ) :
    pkpW (codesW (S.map codeV) w) = evalCodes S w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [codesW, List.map_cons, pkpW_cons, ← codesW, ih, evalCodes]
    congr 1
    split
    · exact pkp_getD_map S _
    · rw [pkp_invV, pkp_getD_map]

end CFSG.Certificates.Kernel.PkEnum

end
