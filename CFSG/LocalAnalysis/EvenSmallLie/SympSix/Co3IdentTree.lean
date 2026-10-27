module

public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem Rep.of_eqA {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (h : eqA n t u = true) : Rep n t g := by
  intro x
  have h1 := allLt_spec h x.2
  rw [beq_iff_eq] at h1
  rw [h1, hu x]

@[expose] def prodA (n : ℕ) (G : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA n
  | i :: w => compA n G[i]! (prodA n G w)

theorem rep_prodA {n : ℕ} {G : Array (Array ℕ)} {x : ℕ → Equiv.Perm (Fin n)}
    (hx : ∀ i < G.size, Rep n G[i]! (x i)) :
    ∀ w : List ℕ, (∀ i ∈ w, i < G.size) → Rep n (prodA n G w) (w.map x).prod
  | [], _ => by simpa [prodA] using (rep_idA (n := n))
  | i :: w, hw => by
    rw [prodA, List.map_cons, List.prod_cons]
    exact rep_compA (hx i (hw i List.mem_cons_self))
      (rep_prodA hx w fun j hj => hw j (List.mem_cons_of_mem _ hj))

section Tree

variable {K : Type*} [Group K]

@[expose] noncomputable def treeEval (par lab : Array ℕ) (x : ℕ → K) (j : ℕ) : K :=
  if _h : 0 < j ∧ par[j]! < j then treeEval par lab x par[j]! * x lab[j]! else 1
termination_by j
decreasing_by exact _h.2

theorem treeEval_eq (par lab : Array ℕ) (x : ℕ → K) (j : ℕ) :
    treeEval par lab x j =
      if 0 < j ∧ par[j]! < j then treeEval par lab x par[j]! * x lab[j]! else 1 := by
  rw [treeEval]
  split <;> simp_all

theorem treeEval_zero (par lab : Array ℕ) (x : ℕ → K) : treeEval par lab x 0 = 1 := by
  rw [treeEval_eq]
  simp

theorem treeEval_of_lt (par lab : Array ℕ) (x : ℕ → K) {j : ℕ} (hj : 0 < j)
    (hp : par[j]! < j) : treeEval par lab x j = treeEval par lab x par[j]! * x lab[j]! := by
  rw [treeEval_eq, ite_eq_left ⟨hj, hp⟩]

theorem map_treeEval {K' : Type*} [Group K'] (f : K →* K') (par lab : Array ℕ) (x : ℕ → K)
    (j : ℕ) : f (treeEval par lab x j) = treeEval par lab (fun i => f (x i)) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [treeEval_eq, treeEval_eq par lab (fun i => f (x i))]
    split
    · rename_i h
      rw [map_mul, ih _ h.2]
    · exact map_one f

theorem treeEval_mem (S : Subgroup K) {x : ℕ → K} (hx : ∀ i, x i ∈ S) (par lab : Array ℕ)
    (j : ℕ) : treeEval par lab x j ∈ S := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [treeEval_eq]
    split
    · rename_i h
      exact S.mul_mem (ih _ h.2) (hx _)
    · exact S.one_mem

theorem treeEval_congr {par lab : Array ℕ} {x x' : ℕ → K} {N k : ℕ}
    (hlab : ∀ j < N, 0 < j → lab[j]! < k) (hxx : ∀ i < k, x i = x' i) :
    ∀ j < N, treeEval par lab x j = treeEval par lab x' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [treeEval_eq, treeEval_eq par lab x']
    split
    · rename_i h
      rw [ih _ h.2 (by omega), hxx _ (hlab j hj h.1)]
    · rfl

end Tree

@[expose] def treeTabOK (n : ℕ) (G : Array (Array ℕ)) (par lab : Array ℕ) (T : Array (Array ℕ))
    (N : ℕ) : Bool :=
  eqA n T[0]! (idA n) && allLt N fun j => j == 0 ||
    (decide (par[j]! < j) && decide (lab[j]! < G.size) &&
      eqA n T[j]! (compA n T[par[j]!]! G[lab[j]!]!))

theorem treeTabOK_spec {n : ℕ} {G : Array (Array ℕ)} {par lab : Array ℕ}
    {T : Array (Array ℕ)} {N : ℕ} (h : treeTabOK n G par lab T N = true) :
    eqA n T[0]! (idA n) = true ∧ ∀ j < N, 0 < j → par[j]! < j ∧ lab[j]! < G.size ∧
      eqA n T[j]! (compA n T[par[j]!]! G[lab[j]!]!) = true := by
  unfold treeTabOK at h
  rw [Bool.and_eq_true, allLt_iff] at h
  refine ⟨h.1, fun j hj hj0 => ?_⟩
  have := h.2 j hj
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h0 | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, h3⟩

theorem rep_treeTab {n : ℕ} {G : Array (Array ℕ)} {par lab : Array ℕ} {T : Array (Array ℕ)}
    {N : ℕ} (h : treeTabOK n G par lab T N = true) {x : ℕ → Equiv.Perm (Fin n)}
    (hx : ∀ i < G.size, Rep n G[i]! (x i)) : ∀ j < N, Rep n T[j]! (treeEval par lab x j) := by
  obtain ⟨h0, hs⟩ := treeTabOK_spec h
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [treeEval_zero]
      exact Rep.of_eqA rep_idA h0
    · obtain ⟨hp, hl, he⟩ := hs j hj hj0
      rw [treeEval_of_lt par lab x hj0 hp]
      exact Rep.of_eqA (rep_compA (ih _ hp (by omega)) (hx _ hl)) he

@[expose] def keyOf (pts : List ℕ) (t : Array ℕ) : ℕ :=
  pts.foldl (fun acc p => acc * 276 + t[p]!) 0

@[expose] def strictInc : List ℕ → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def keysOK (pts : List ℕ) (T : Array (Array ℕ)) (N : ℕ) : Bool :=
  strictInc (((List.range N).map fun j => keyOf pts T[j]!).mergeSort fun a b => decide (a ≤ b))

theorem pairwise_of_strictInc : ∀ l : List ℕ, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictInc (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

theorem keyOf_congr {pts : List ℕ} {t u : Array ℕ} (h : ∀ q ∈ pts, t[q]! = u[q]!) :
    keyOf pts t = keyOf pts u := by
  unfold keyOf
  generalize 0 = acc
  induction pts generalizing acc with
  | nil => rfl
  | cons q pts ih =>
    simp only [List.foldl_cons]
    rw [h q List.mem_cons_self]
    exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) _

theorem eq_of_keysOK {pts : List ℕ} {T : Array (Array ℕ)} {N : ℕ} (h : keysOK pts T N = true)
    {i j : ℕ} (hi : i < N) (hj : j < N) (hk : keyOf pts T[i]! = keyOf pts T[j]!) : i = j := by
  have hnd : ((List.range N).map fun j => keyOf pts T[j]!).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 (pairwise_of_strictInc _ h).nodup
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) hk

theorem eq_of_rep_of_keysOK {n : ℕ} {pts : List ℕ} (hpts : ∀ q ∈ pts, q < n)
    {T : Array (Array ℕ)} {N : ℕ} (h : keysOK pts T N = true) {i j : ℕ} (hi : i < N)
    (hj : j < N) {g : Equiv.Perm (Fin n)} (hgi : Rep n T[i]! g) (hgj : Rep n T[j]! g) :
    i = j :=
  eq_of_keysOK h hi hj (keyOf_congr fun q hq => by
    rw [hgi.apply (hpts q hq), hgj.apply (hpts q hq)])

end CFSG.EvenSmallLie.SympSix.Co3Ident
