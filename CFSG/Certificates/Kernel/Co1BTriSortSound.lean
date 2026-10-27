module

public import CFSG.Certificates.Kernel.MergeReplaySound

public section

namespace CFSG.KC.Co1B

open CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1Schreier.Native

theorem vSorted_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → vSorted l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    rw [List.pairwise_cons] at h
    simp only [vSorted, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1 b List.mem_cons_self, vSorted_of_pairwise h.2⟩

theorem pairwise_of_vSorted : ∀ {l : List Nat}, vSorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    simp only [vSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_vSorted h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.1 ih).1 c hc)

theorem vSorted_mergeSort {l : List Nat} (h : l.Nodup) :
    vSorted (l.mergeSort fun a b => decide (a ≤ b)) = true := by
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hnd : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.2 h
  refine vSorted_of_pairwise ((hs.and hnd).imp fun hab => ?_)
  simp only [decide_eq_true_eq] at hab
  omega

theorem nodup_of_vSorted {l l' : List Nat} (h : vSorted l' = true) (hp : l'.Perm l) : l.Nodup :=
  hp.nodup_iff.1 ((pairwise_of_vSorted h).imp Nat.ne_of_lt)

@[expose] def tstep (tab : Array Nat) (p : (Nat × Nat) × Nat) : Array Nat :=
  ((tab.set! p.1.1 p.2).set! p.1.2 p.2).set! (p.1.1 ^^^ p.1.2) p.2

@[expose] def tpos (p : (Nat × Nat) × Nat) : List Nat := [p.1.1, p.1.2, p.1.1 ^^^ p.1.2]

theorem triTable_eq (T : List (Nat × Nat)) :
    triTable T = T.zipIdx.foldl tstep (Array.replicate (2 ^ 24) 1365) := by
  simp [triTable]
  rfl

theorem tstep_size (tab : Array Nat) (p : (Nat × Nat) × Nat) : (tstep tab p).size = tab.size := by
  simp [tstep]

theorem foldl_size (tab : Array Nat) :
    ∀ L : List ((Nat × Nat) × Nat), (L.foldl tstep tab).size = tab.size
  | [] => rfl
  | p :: L => by rw [List.foldl_cons, foldl_size _ L, tstep_size]

theorem tstep_get {tab : Array Nat} {p : (Nat × Nat) × Nat} (hp : ∀ y ∈ tpos p, y < tab.size)
    (y : Nat) : (tstep tab p)[y]! = if y ∈ tpos p then p.2 else tab[y]! := by
  have h1 := hp p.1.1 (by simp [tpos])
  have h2 := hp p.1.2 (by simp [tpos])
  have h3 := hp (p.1.1 ^^^ p.1.2) (by simp [tpos])
  unfold tstep
  rw [CFSG.KC.MergeR.set_get (by simpa using h3), CFSG.KC.MergeR.set_get (by simpa using h2),
    CFSG.KC.MergeR.set_get h1]
  by_cases e3 : y = p.1.1 ^^^ p.1.2
  · simp [e3, tpos]
  · by_cases e2 : y = p.1.2
    · simp [e2, tpos]
    · by_cases e1 : y = p.1.1
      · simp [e1, tpos]
      · simp [e1, e2, e3, tpos]

theorem foldl_keep {y : Nat} :
    ∀ (L : List ((Nat × Nat) × Nat)) (tab : Array Nat), (∀ q ∈ L, ∀ z ∈ tpos q, z < tab.size) →
      (∀ q ∈ L, y ∉ tpos q) → (L.foldl tstep tab)[y]! = tab[y]!
  | [], _, _, _ => rfl
  | p :: L, tab, hs, hy => by
    rw [List.foldl_cons, foldl_keep L _ (fun q hq z hz => by
        rw [tstep_size]; exact hs q (List.mem_cons_of_mem p hq) z hz)
      (fun q hq => hy q (List.mem_cons_of_mem p hq)),
      tstep_get (hs p List.mem_cons_self), ite_eq_right (hy p List.mem_cons_self)]

theorem foldl_write {y : Nat} :
    ∀ (L : List ((Nat × Nat) × Nat)) (tab : Array Nat), (∀ q ∈ L, ∀ z ∈ tpos q, z < tab.size) →
      (L.flatMap tpos).Nodup → ∀ q ∈ L, y ∈ tpos q → (L.foldl tstep tab)[y]! = q.2
  | [], _, _, _, q, hq, _ => absurd hq List.not_mem_nil
  | p :: L, tab, hs, hnd, q, hq, hy => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    have hs' : ∀ q ∈ L, ∀ z ∈ tpos q, z < (tstep tab p).size := fun q hq z hz => by
      rw [tstep_size]
      exact hs q (List.mem_cons_of_mem p hq) z hz
    rw [List.foldl_cons]
    by_cases hqL : q ∈ L
    · exact foldl_write L _ hs' hnd.2.1 q hqL hy
    · obtain rfl : q = p := by
        rcases List.mem_cons.1 hq with h | h
        · exact h
        · exact absurd h hqL
      rw [foldl_keep L _ hs' (fun r hr hyr => hnd.2.2 y hy y
          (List.mem_flatMap.2 ⟨r, hr, hyr⟩) rfl),
        tstep_get (hs q List.mem_cons_self), ite_eq_left hy]

theorem flatMap_tpos (T : List (Nat × Nat)) : T.zipIdx.flatMap tpos = triVecs T := by
  unfold triVecs
  conv_rhs => rw [← List.zipIdx_map_fst 0 T]
  rw [List.flatMap_map]
  rfl

theorem triTable_get {T : List (Nat × Nat)} (hnd : (triVecs T).Nodup)
    (hlt : ∀ y ∈ triVecs T, y < 2 ^ 24) {k : Nat} (hk : k < T.length) {y : Nat}
    (hy : y ∈ [T[k].1, T[k].2, T[k].1 ^^^ T[k].2]) : (triTable T)[y]! = k := by
  have hmem : (T[k], k) ∈ T.zipIdx := List.mem_zipIdx_iff_getElem?.2 (by simp)
  have hs : ∀ q ∈ T.zipIdx, ∀ z ∈ tpos q, z < (Array.replicate (2 ^ 24) 1365).size :=
    fun q hq z hz => by
      rw [Array.size_replicate]
      exact hlt z (by rw [← flatMap_tpos]; exact List.mem_flatMap.2 ⟨q, hq, hz⟩)
  rw [triTable_eq]
  exact foldl_write _ _ hs (by rw [flatMap_tpos]; exact hnd) _ hmem hy

theorem tableOK_triTable {T : List (Nat × Nat)} (hnd : (triVecs T).Nodup)
    (hlt : ∀ y ∈ triVecs T, y < 2 ^ 24) : tableOK (triTable T) T = true := by
  unfold tableOK
  rw [List.all_eq_true]
  intro p hp
  have hk : p.2 < T.length := List.snd_lt_of_mem_zipIdx hp
  have he : T[p.2] = p.1 := by
    have := List.mem_zipIdx_iff_getElem?.1 hp
    exact (List.getElem?_eq_some_iff.1 this).2
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> exact triTable_get hnd hlt hk (by simp [he])

end CFSG.KC.Co1B

end
