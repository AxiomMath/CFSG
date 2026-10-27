module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

public section

namespace CFSG.Certificates.SetOrbit

open CFSG.Monster.B.Co2
open scoped Pointwise

@[expose] def ltChain : List ℕ → Bool
  | a :: b :: l => decide (a < b) && ltChain (b :: l)
  | _ => true

@[expose] def imgList (g s : Array ℕ) : List ℕ := (s.toList.map fun x => g[x]!).mergeSort Nat.ble

@[expose] def entryOK (n m : ℕ) (s : Array ℕ) : Bool :=
  s.size == m && s.toList.all (· < n) && ltChain s.toList

@[expose] def boundOK (N : ℕ) (ind : Array ℕ) : Bool :=
  ind.size == N && (List.range N).all fun i => decide (ind[i]! < N)

@[expose] def lexChain : List (List ℕ) → Bool
  | a :: b :: l => decide (a < b) && lexChain (b :: l)
  | _ => true

@[expose] def distinctOK (tab : Array (Array ℕ)) : Bool :=
  lexChain ((tab.toList.map Array.toList).mergeSort (fun a b => decide (a ≤ b)))

@[expose] def keyL : List ℕ → ℕ
  | a :: b :: c :: d :: e :: _ => (((a * 4096 + b) * 4096 + c) * 4096 + d) * 4096 + e
  | _ => 0

@[expose] def keyMap (tab : Array (Array ℕ)) : Std.HashMap ℕ (List ℕ) :=
  (List.range tab.size).foldl (fun m i =>
    let k := keyL (tab[i]!).toList
    m.insert k (i :: m.getD k [])) ∅

@[expose] def lookupIdx (tab : Array (Array ℕ)) (m : Std.HashMap ℕ (List ℕ)) (t : List ℕ) : ℕ :=
  match (m.getD (keyL t) []).find? (fun j => decide ((tab[j]!).toList = t)) with
  | some j => j
  | none => tab.size

@[expose] def induceL (tab : Array (Array ℕ)) (m : Std.HashMap ℕ (List ℕ)) (g : Array ℕ) :
    Array ℕ :=
  tab.map fun s => lookupIdx tab m (imgList g s)

@[expose] def bfsL (gens : Array (Array ℕ)) (root : Array ℕ) (fuel : ℕ) : Array (Array ℕ) :=
  Id.run do
    let mut tab : Array (Array ℕ) := #[root]
    let mut m : Std.HashMap ℕ (List ℕ) :=
      (∅ : Std.HashMap ℕ (List ℕ)).insert (keyL root.toList) [0]
    let mut i := 0
    for _ in [0:fuel] do
      if i < tab.size then
        let s := tab[i]!
        for g in gens do
          let t := imgList g s
          let k := keyL t
          let cands := m.getD k []
          let found := cands.any fun j => decide ((tab[j]!).toList = t)
          if !found then
            m := m.insert k (tab.size :: cands)
            tab := tab.push t.toArray
        i := i + 1
    return tab

@[expose] def ptSet (n : ℕ) (s : Array ℕ) : Set (Fin n) := {x | (x : ℕ) ∈ s.toList}

theorem pairwise_of_ltChain : ∀ {l : List ℕ}, ltChain l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ltChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_ltChain h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

theorem entryOK_lt {n m : ℕ} {s : Array ℕ} (h : entryOK n m s = true) : ∀ x ∈ s.toList, x < n := by
  simp only [entryOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem entryOK_size {n m : ℕ} {s : Array ℕ} (h : entryOK n m s = true) : s.size = m := by
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem entryOK_pairwise {n m : ℕ} {s : Array ℕ} (h : entryOK n m s = true) :
    s.toList.Pairwise (· < ·) := by
  simp only [entryOK, Bool.and_eq_true] at h
  exact pairwise_of_ltChain h.2

theorem mem_ptSet {n : ℕ} {s : Array ℕ} {x : Fin n} : x ∈ ptSet n s ↔ (x : ℕ) ∈ s.toList :=
  Iff.rfl

theorem mem_imgList {g s : Array ℕ} {y : ℕ} : y ∈ imgList g s ↔ ∃ x ∈ s.toList, g[x]! = y := by
  rw [imgList, List.mem_mergeSort, List.mem_map]

theorem ptSet_of_toList_eq_imgList {n : ℕ} {g s t : Array ℕ} {σ : Equiv.Perm (Fin n)}
    (hg : Rep n g σ) (hs : ∀ x ∈ s.toList, x < n) (h : t.toList = imgList g s) :
    ptSet n t = σ • ptSet n s := by
  ext x
  rw [mem_ptSet, h, mem_imgList, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨⟨y, hs y hy⟩, hy, ?_⟩
    rw [Equiv.Perm.smul_def]
    apply Fin.ext
    rw [← hxy, hg.apply (hs y hy)]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [Equiv.Perm.smul_def, hg.apply y.2]

theorem eq_of_ptSet_eq {n m : ℕ} {s t : Array ℕ} (hs : entryOK n m s = true)
    (ht : entryOK n m t = true) (h : ptSet n s = ptSet n t) : s = t := by
  apply Array.toList_inj.1
  refine (entryOK_pairwise hs).eq_of_mem_iff (entryOK_pairwise ht) fun a => ?_
  constructor
  · intro ha
    have := (Set.ext_iff.1 h ⟨a, entryOK_lt hs a ha⟩).1 ha
    exact this
  · intro ha
    have := (Set.ext_iff.1 h ⟨a, entryOK_lt ht a ha⟩).2 ha
    exact this

theorem lookupIdx_spec {tab : Array (Array ℕ)} {m : Std.HashMap ℕ (List ℕ)} {t : List ℕ}
    (h : lookupIdx tab m t < tab.size) : (tab[lookupIdx tab m t]!).toList = t := by
  unfold lookupIdx at h ⊢
  cases hf : (m.getD (keyL t) []).find? (fun j => decide ((tab[j]!).toList = t)) with
  | none =>
    rw [hf] at h
    exact absurd h (lt_irrefl _)
  | some j =>
    have := List.find?_some hf
    simpa using this

theorem induceL_get {tab : Array (Array ℕ)} {m : Std.HashMap ℕ (List ℕ)} {g : Array ℕ} {i : ℕ}
    (hi : i < tab.size) : (induceL tab m g)[i]! = lookupIdx tab m (imgList g tab[i]!) := by
  rw [induceL, getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos tab i hi]

theorem induceL_spec {tab : Array (Array ℕ)} {m : Std.HashMap ℕ (List ℕ)} {g : Array ℕ} {i : ℕ}
    (hi : i < tab.size) (hlt : (induceL tab m g)[i]! < tab.size) :
    (tab[(induceL tab m g)[i]!]!).toList = imgList g tab[i]! := by
  rw [induceL_get hi] at hlt ⊢
  exact lookupIdx_spec hlt

theorem boundOK_spec {N : ℕ} {ind : Array ℕ} (h : boundOK N ind = true) {i : ℕ} (hi : i < N) :
    ind[i]! < N := by
  simp only [boundOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.2 i hi

theorem pairwise_of_lexChain : ∀ {l : List (List ℕ)}, lexChain l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [lexChain, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_lexChain h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact List.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem distinctOK_spec {tab : Array (Array ℕ)} (h : distinctOK tab = true) {i j : ℕ}
    (hi : i < tab.size) (hj : j < tab.size) (e : tab[i]! = tab[j]!) : i = j := by
  have hp := pairwise_of_lexChain h
  have hnd : ((tab.toList.map Array.toList).mergeSort (fun a b => decide (a ≤ b))).Nodup :=
    hp.imp fun hab => ne_of_lt hab
  have hnd' : (tab.toList.map Array.toList).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 hnd
  have hnd'' : tab.toList.Nodup := List.Nodup.of_map _ hnd'
  rw [getElem!_pos tab i hi, getElem!_pos tab j hj] at e
  have := (List.Nodup.getElem_inj_iff hnd'' (i := i) (j := j) (hi := by simpa using hi)
    (hj := by simpa using hj)).1 (by simpa using e)
  exact this

end CFSG.Certificates.SetOrbit
