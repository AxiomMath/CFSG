module

public import CFSG.Perm.OrbitTree

public section

namespace CFSG.Certificates.IndexOrbit

structure IdxOrbit where
  pts : Array ℕ
  par : Array ℕ
  lab : Array ℕ
  deriving Inhabited

@[expose] def idxTreeOK (inds : Array (Array ℕ)) (o : IdxOrbit) : Bool :=
  decide (0 < o.pts.size) && (List.range o.pts.size).all fun t =>
    t == 0 || (decide (o.par[t]! < t) && decide (o.lab[t]! < inds.size) &&
      (inds[o.lab[t]!]!)[o.pts[o.par[t]!]!]! == o.pts[t]!)

@[expose] def idxClosedOK (inds : Array (Array ℕ)) (o : IdxOrbit) (pos : Array ℕ) : Bool :=
  (List.range o.pts.size).all fun t => (List.range inds.size).all fun r =>
    decide (pos[(inds[r]!)[o.pts[t]!]!]! < o.pts.size) &&
      o.pts[pos[(inds[r]!)[o.pts[t]!]!]!]! == (inds[r]!)[o.pts[t]!]!

@[expose] def idxPartitionOK (N : ℕ) (orbs : Array IdxOrbit) (oid pos : Array ℕ) : Bool :=
  ((List.range N).all fun i => decide (oid[i]! < orbs.size) &&
      decide (pos[i]! < (orbs[oid[i]!]!).pts.size) && (orbs[oid[i]!]!).pts[pos[i]!]! == i) &&
    (List.range orbs.size).all fun c => (List.range (orbs[c]!).pts.size).all fun t =>
      decide ((orbs[c]!).pts[t]! < N) && oid[(orbs[c]!).pts[t]!]! == c &&
        pos[(orbs[c]!).pts[t]!]! == t

@[expose] def idxOrbits (inds : Array (Array ℕ)) (N : ℕ) :
    Array IdxOrbit × Array ℕ × Array ℕ := Id.run do
  let mut oid : Array ℕ := Array.replicate N N
  let mut pos : Array ℕ := Array.replicate N 0
  let mut orbs : Array IdxOrbit := #[]
  for s in [0:N] do
    if oid[s]! == N then
      let c := orbs.size
      let mut pts : Array ℕ := #[s]
      let mut par : Array ℕ := #[0]
      let mut lab : Array ℕ := #[0]
      oid := oid.set! s c
      pos := pos.set! s 0
      let mut t := 0
      for _ in [0:N] do
        if t < pts.size then
          let x := pts[t]!
          for r in [0:inds.size] do
            let y := (inds[r]!)[x]!
            if y < N && oid[y]! == N then
              oid := oid.set! y c
              pos := pos.set! y pts.size
              pts := pts.push y
              par := par.push t
              lab := lab.push r
          t := t + 1
      orbs := orbs.push ⟨pts, par, lab⟩
  return (orbs, oid, pos)

section Soundness

variable {G X : Type*} [Group G] [MulAction G X]

theorem idxTreeOK_spec {inds : Array (Array ℕ)} {o : IdxOrbit} (h : idxTreeOK inds o = true) :
    0 < o.pts.size ∧ ∀ t, 0 < t → t < o.pts.size → o.par[t]! < t ∧ o.lab[t]! < inds.size ∧
      (inds[o.lab[t]!]!)[o.pts[o.par[t]!]!]! = o.pts[t]! := by
  simp only [idxTreeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun t ht0 ht => ?_⟩
  rcases h.2 t ht with h0 | h1
  · omega
  · exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem idxClosedOK_spec {inds : Array (Array ℕ)} {o : IdxOrbit} {pos : Array ℕ}
    (h : idxClosedOK inds o pos = true) {t r : ℕ} (ht : t < o.pts.size) (hr : r < inds.size) :
    pos[(inds[r]!)[o.pts[t]!]!]! < o.pts.size ∧
      o.pts[pos[(inds[r]!)[o.pts[t]!]!]!]! = (inds[r]!)[o.pts[t]!]! := by
  simp only [idxClosedOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h t ht r hr

theorem orbit_of_idxOrbit {inds : Array (Array ℕ)} {o : IdxOrbit} {pos : Array ℕ} {σ : ℕ → G}
    {dec : ℕ → X} (hact : ∀ r < inds.size, ∀ t < o.pts.size,
      dec ((inds[r]!)[o.pts[t]!]!) = σ r • dec o.pts[t]!)
    (htree : idxTreeOK inds o = true) (hcl : idxClosedOK inds o pos = true) :
    MulAction.orbit (Subgroup.closure (σ '' {r | r < inds.size})) (dec o.pts[0]!) =
      (fun t => dec o.pts[t]!) '' {t | t < o.pts.size} := by
  obtain ⟨hpos, htr⟩ := idxTreeOK_spec htree
  refine CFSG.Perm.orbit_closure_eq_image (P := fun t => dec o.pts[t]!) hpos ?_
    (τ := CFSG.Perm.treeWord (fun t => o.par[t]!) (fun t => o.lab[t]!) σ) ?_ ?_
  · rintro t ht _ ⟨r, hr, rfl⟩
    obtain ⟨h1, h2⟩ := idxClosedOK_spec hcl ht hr
    exact ⟨_, h1, by beta_reduce; rw [h2, hact r hr t ht]⟩
  · intro t ht
    exact CFSG.Perm.treeWord_mem (n := o.pts.size) (fun t h0 hts => (htr t h0 hts).1)
      (fun t h0 hts => Subgroup.subset_closure (Set.mem_image_of_mem σ (htr t h0 hts).2.1)) ht
  · intro t ht
    refine CFSG.Perm.treeWord_smul (n := o.pts.size) (P := fun t => dec o.pts[t]!)
      (fun t h0 hts => (htr t h0 hts).1) (fun t h0 hts => ?_) ht
    obtain ⟨hp, hl, he⟩ := htr t h0 hts
    show dec o.pts[t]! = σ o.lab[t]! • dec o.pts[o.par[t]!]!
    rw [← he, hact _ hl _ (hp.trans hts)]

theorem idxPartitionOK_spec {N : ℕ} {orbs : Array IdxOrbit} {oid pos : Array ℕ}
    (h : idxPartitionOK N orbs oid pos = true) :
    (∀ i < N, oid[i]! < orbs.size ∧ pos[i]! < (orbs[oid[i]!]!).pts.size ∧
      (orbs[oid[i]!]!).pts[pos[i]!]! = i) ∧
    (∀ c < orbs.size, ∀ t < (orbs[c]!).pts.size,
      (orbs[c]!).pts[t]! < N ∧ oid[(orbs[c]!).pts[t]!]! = c ∧ pos[(orbs[c]!).pts[t]!]! = t) := by
  simp only [idxPartitionOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨fun i hi => ⟨(h.1 i hi).1.1, (h.1 i hi).1.2, (h.1 i hi).2⟩,
    fun c hc t ht => ⟨(h.2 c hc t ht).1.1, (h.2 c hc t ht).1.2, (h.2 c hc t ht).2⟩⟩

end Soundness

end CFSG.Certificates.IndexOrbit
