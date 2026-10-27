
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase

public section

namespace CFSG.KC.Orb14

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census

section Fold

variable {α : Type} (f : ℕ → Array α → α)

def pushF (n : ℕ) : Array α := (List.range n).foldl (fun acc i => acc.push (f i acc)) #[]

theorem pushF_succ (n : ℕ) : pushF f (n + 1) = (pushF f n).push (f n (pushF f n)) := by
  simp only [pushF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pushF_size : ∀ n, (pushF f n).size = n
  | 0 => rfl
  | n + 1 => by rw [pushF_succ, Array.size_push, pushF_size n]

theorem pushF_get [Inhabited α] : ∀ {n i : ℕ}, i < n → (pushF f n)[i]! = f i (pushF f i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    rw [pushF_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [getElem!_pos _ i (by rw [Array.size_push, pushF_size]; omega),
        Array.getElem_push_lt (by rw [pushF_size]; exact h), ← getElem!_pos, pushF_get h]
    · rw [getElem!_pos _ i (by rw [Array.size_push, pushF_size]; omega), Array.getElem_push,
        dite_eq_right (by rw [pushF_size]; omega)]

theorem pushF_prefix [Inhabited α] {n i j : ℕ} (hj : j < i) (hi : i ≤ n) : (pushF f n)[j]! = (pushF f i)[j]! := by
  rw [pushF_get f (by omega : j < n), pushF_get f hj]

end Fold

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (g : α → β) {a : Array α} {x : ℕ}
    (h : x < a.size) : (a.map g)[x]! = g a[x]! := by
  rw [getElem!_pos _ x (by rw [Array.size_map]; exact h), Array.getElem_map, getElem!_pos a x h]

theorem range_get {N x : ℕ} (h : x < N) : (List.range N).toArray[x]! = x := by
  rw [getElem!_pos _ x (by simpa using h), List.getElem_toArray, List.getElem_range]

structure PermGens (gen : Array (Array ℕ)) (N : ℕ) : Prop where
  lt : ∀ k < 17, ∀ x < N, (gen[k]!)[x]! < N
  inj : ∀ k < 17, ∀ x < N, ∀ y < N, (gen[k]!)[x]! = (gen[k]!)[y]! → x = y

@[expose] def TreeShape : Prop := ∀ i, 0 < i → i < 1408 → tauPar i < i ∧ tauLab i < 17

@[expose] def transF (gen : Array (Array ℕ)) (N : ℕ) (i : ℕ) (acc : Array (Array ℕ)) : Array ℕ :=
  if i = 0 then (List.range N).toArray else (acc[tauPar i]!).map fun x => (gen[tauLab i]!)[x]!

theorem transArr_eq (gen : Array (Array ℕ)) (N : ℕ) :
    transArr gen N = pushF (transF gen N) 1408 := by
  unfold transArr pushF
  exact congrArg (fun f => List.foldl f #[] (List.range 1408))
    (funext fun acc => funext fun i => rfl)

theorem transArr_size (gen : Array (Array ℕ)) (N : ℕ) : (transArr gen N).size = 1408 := by
  rw [transArr_eq, pushF_size]

theorem transArr_get {gen : Array (Array ℕ)} {N : ℕ} (htr : TreeShape) {i : ℕ} (hi : i < 1408) :
    (transArr gen N)[i]! = if i = 0 then (List.range N).toArray
      else ((transArr gen N)[tauPar i]!).map fun x => (gen[tauLab i]!)[x]! := by
  rw [transArr_eq, pushF_get _ hi]
  change (if i = 0 then _ else _) = _
  split
  · rfl
  · next h0 =>
    rw [pushF_prefix (n := 1408) (i := i) _ (htr i (Nat.pos_of_ne_zero h0) hi).1 (by omega)]

structure IsPermArr (p : Array ℕ) (N : ℕ) : Prop where
  size : p.size = N
  lt : ∀ x < N, p[x]! < N
  inj : ∀ x < N, ∀ y < N, p[x]! = p[y]! → x = y

theorem transArr_zero {gen : Array (Array ℕ)} {N : ℕ} (htr : TreeShape) {x : ℕ} (hx : x < N) :
    ((transArr gen N)[0]!)[x]! = x := by
  rw [transArr_get htr (by norm_num), ite_eq_left rfl, range_get hx]

theorem transArr_step {gen : Array (Array ℕ)} {N : ℕ} (htr : TreeShape) {i : ℕ} (h0 : 0 < i)
    (hi : i < 1408) (hp : ((transArr gen N)[tauPar i]!).size = N) {x : ℕ} (hx : x < N) :
    ((transArr gen N)[i]!)[x]! = (gen[tauLab i]!)[((transArr gen N)[tauPar i]!)[x]!]! := by
  rw [transArr_get htr hi, ite_eq_right (by omega), getElem!_map' _ (by rw [hp]; exact hx)]

theorem transArr_perm {gen : Array (Array ℕ)} {N : ℕ} (hg : PermGens gen N) (htr : TreeShape) :
    ∀ i < 1408, IsPermArr (transArr gen N)[i]! N := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · refine ⟨?_, fun x hx => ?_, fun x hx y hy e => ?_⟩
      · rw [transArr_get htr hi, ite_eq_left rfl]
        simp
      · rw [transArr_zero htr hx]
        exact hx
      · rwa [transArr_zero htr hx, transArr_zero htr hy] at e
    · obtain ⟨hp, hl⟩ := htr i h0 hi
      have ihp := ih _ hp (hp.trans hi)
      refine ⟨?_, fun x hx => ?_, fun x hx y hy e => ?_⟩
      · rw [transArr_get htr hi, ite_eq_right (by omega), Array.size_map, ihp.size]
      · rw [transArr_step htr h0 hi ihp.size hx]
        exact hg.lt _ hl _ (ihp.lt x hx)
      · rw [transArr_step htr h0 hi ihp.size hx, transArr_step htr h0 hi ihp.size hy] at e
        exact ihp.inj x hx y hy (hg.inj _ hl _ (ihp.lt x hx) _ (ihp.lt y hy) e)

def invF (p : Array ℕ) (m : ℕ) : Array ℕ :=
  (List.range m).foldl (fun acc x => acc.set! p[x]! x) (Array.replicate p.size 0)

theorem invF_succ (p : Array ℕ) (m : ℕ) : invF p (m + 1) = (invF p m).set! p[m]! m := by
  simp only [invF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem invF_size (p : Array ℕ) : ∀ m, (invF p m).size = p.size
  | 0 => by simp [invF]
  | m + 1 => by rw [invF_succ, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, invF_size p m]

theorem invF_get {p : Array ℕ} {N : ℕ} (hp : IsPermArr p N) :
    ∀ m ≤ N, ∀ x < m, (invF p m)[p[x]!]! = x := by
  intro m
  induction m with
  | zero => intro _ x hx; omega
  | succ m ih =>
    intro hm x hx
    have hsz : p[m]! < (invF p m).size := by rw [invF_size, hp.size]; exact hp.lt m (by omega)
    rw [invF_succ, Array.set!_eq_setIfInBounds]
    have hxs : p[x]! < (invF p m).size := by rw [invF_size, hp.size]; exact hp.lt x (by omega)
    rw [getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; exact hxs),
      Array.getElem_setIfInBounds hxs]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
    · rw [ite_eq_right (fun e => by have := hp.inj m (by omega) x (by omega) e; omega),
        ← getElem!_pos, ih (by omega) x hx]
    · rw [ite_eq_left rfl]

theorem perm_surj {p : Array ℕ} {N : ℕ} (hp : IsPermArr p N) :
    ∀ y < N, ∃ x < N, p[x]! = y := by
  have hsub : (Finset.range N).image (fun x => p[x]!) ⊆ Finset.range N := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hp.lt x (Finset.mem_range.1 hx))
  have hcard : (Finset.range N).card ≤ ((Finset.range N).image (fun x => p[x]!)).card := by
    rw [Finset.card_image_of_injOn (fun a ha b hb e =>
      hp.inj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)]
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  intro y hy
  have : y ∈ (Finset.range N).image (fun x => p[x]!) := by rw [he]; exact Finset.mem_range.2 hy
  obtain ⟨x, hx, e⟩ := Finset.mem_image.1 this
  exact ⟨x, Finset.mem_range.1 hx, e⟩

theorem invPermArr_spec {p : Array ℕ} {N : ℕ} (hp : IsPermArr p N) :
    ∀ y < N, (invPermArr p)[y]! < N ∧ p[(invPermArr p)[y]!]! = y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := perm_surj hp y hy
  have e : invPermArr p = invF p N := by rw [← hp.size]; rfl
  rw [e, invF_get hp N le_rfl x hx]
  exact ⟨hx, rfl⟩

theorem invPermArr_left {p : Array ℕ} {N : ℕ} (hp : IsPermArr p N) {x : ℕ} (hx : x < N) :
    (invPermArr p)[p[x]!]! = x := by
  obtain ⟨h1, h2⟩ := invPermArr_spec hp _ (hp.lt x hx)
  exact hp.inj _ h1 _ hx h2

theorem treeOK_of_perm {gen : Array (Array ℕ)} {N : ℕ} (hg : PermGens gen N) (htr : TreeShape) :
    treeOK gen (transArr gen N) ((transArr gen N).map invPermArr) N = true := by
  have hI : ∀ i < 1408, ((transArr gen N).map invPermArr)[i]! = invPermArr (transArr gen N)[i]! :=
    fun i hi => getElem!_map' _ (by rw [transArr_size]; exact hi)
  simp only [treeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨fun x hx => transArr_zero htr hx, fun i hi x hx => ?_⟩
  have hp := transArr_perm hg htr i hi
  obtain ⟨h1, h2⟩ := invPermArr_spec hp x hx
  rw [hI i hi]
  refine ⟨⟨⟨hp.lt x hx, h1⟩, h2⟩, ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact Or.inl rfl
  · exact Or.inr (transArr_step htr h0 hi (transArr_perm hg htr _
      ((htr i h0 hi).1.trans hi)).size hx)

theorem schreierOK_of_sets {gen : Array (Array ℕ)} {N : ℕ} (hg : PermGens gen N) (htr : TreeShape)
    {part : Array ℕ} (hpart : ∀ x < N, part[x]! = 0 ∨ part[x]! = 1) (mem : ℕ → ℕ → Prop)
    (h0 : ∀ x < N, mem 0 x ↔ part[x]! = 0)
    (hlt : ∀ i < 1408, ∀ k < 17, tauEdge i k < 1408)
    (hedge : ∀ i < 1408, ∀ k < 17, ∀ y < N,
      mem (tauEdge i k) y ↔ ∃ x < N, (gen[k]!)[x]! = y ∧ mem i x)
    (htreeE : ∀ i, 0 < i → i < 1408 → tauEdge (tauPar i) (tauLab i) = i) :
    schreierOK gen (transArr gen N) ((transArr gen N).map invPermArr) part N = true := by
  have hT := transArr_perm hg htr
  have key : ∀ i < 1408, ∀ x < N, mem i (((transArr gen N)[i]!)[x]!) ↔ part[x]! = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi x hx
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [transArr_zero htr hx]
        exact h0 x hx
      · obtain ⟨hp, hl⟩ := htr i hpos hi
        have hpi := hT _ (hp.trans hi)
        have hE := hedge _ (hp.trans hi) _ hl _ (hg.lt _ hl _ (hpi.lt x hx))
        rw [htreeE i hpos hi] at hE
        rw [transArr_step htr hpos hi hpi.size hx, hE]
        constructor
        · rintro ⟨x', hx', e, hm⟩
          rw [hg.inj _ hl _ hx' _ (hpi.lt x hx) e] at hm
          exact (ih _ hp (hp.trans hi) x hx).1 hm
        · intro h
          exact ⟨_, hpi.lt x hx, rfl, (ih _ hp (hp.trans hi) x hx).2 h⟩
  simp only [schreierOK, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi k hk x hx
  have hj := hlt i hi k hk
  have hTj := hT _ hj
  have hTi := hT i hi
  have hy : (gen[k]!)[((transArr gen N)[i]!)[x]!]! < N := hg.lt k hk _ (hTi.lt x hx)
  rw [getElem!_map' _ (by rw [transArr_size]; exact hj)]
  obtain ⟨hz, hzz⟩ := invPermArr_spec hTj _ hy
  have e1 := key _ hj _ hz
  rw [hzz, hedge i hi k hk _ hy] at e1
  have e2 : (∃ x' < N, (gen[k]!)[x']! = (gen[k]!)[((transArr gen N)[i]!)[x]!]! ∧ mem i x') ↔
      part[x]! = 0 := by
    constructor
    · rintro ⟨x', hx', e, hm⟩
      rw [hg.inj _ hk _ hx' _ (hTi.lt x hx) e] at hm
      exact (key i hi x hx).1 hm
    · intro h
      exact ⟨_, hTi.lt x hx, rfl, (key i hi x hx).2 h⟩
  have e3 := e1.symm.trans e2
  rcases hpart _ hz with h | h <;> rcases hpart x hx with h' | h'
  · rw [h, h']
  · exact absurd (e3.1 h) (by rw [h']; decide)
  · exact absurd (e3.2 h') (by rw [h]; decide)
  · rw [h, h']

end CFSG.KC.Orb14

end
