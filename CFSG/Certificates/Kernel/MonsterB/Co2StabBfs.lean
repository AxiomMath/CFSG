module

public import CFSG.Certificates.Kernel.Spor.RawOrbBfs

public section

namespace CFSG.KS.Co2Stab

open CFSG.Monster.B.Co2.Native CFSG.KS.Raw CFSG.KS.Raw.Orb

structure RecFacts (n root : Nat) (gens : Array (Array Nat)) (dep par lab : Array Nat) : Prop where
  root_pos : 0 < dep[root]!
  one : ∀ z < n, dep[z]! = 1 → z = root
  edge : ∀ z < n, 0 < dep[z]! → dep[z]! ≠ 1 → par[z]! < n ∧ 0 < dep[par[z]!]! ∧
    dep[par[z]!]! + 1 = dep[z]! ∧ lab[z]! < gens.size ∧ (gens[lab[z]!]!)[par[z]!]! = z
  closed : ∀ z < n, 0 < dep[z]! → ∀ j < gens.size, 0 < dep[(gens[j]!)[z]!]!

structure RInv (n root : Nat) (gens : Array (Array Nat)) (a j : Nat) (dep par lab q : Array Nat) :
    Prop where
  dep_size : dep.size = n
  par_size : par.size = n
  lab_size : lab.size = n
  q_pos : 0 < q.size
  q_zero : q[0]! = root
  q_le : q.size ≤ n
  qmem : ∀ k < q.size, q[k]! < n ∧ 0 < dep[q[k]!]!
  qall : ∀ z < n, 0 < dep[z]! → ∃ k < q.size, q[k]! = z
  qinj : ∀ k < q.size, ∀ k' < q.size, q[k]! = q[k']! → k = k'
  root_one : dep[root]! = 1
  one : ∀ z < n, dep[z]! = 1 → z = root
  edge : ∀ z < n, 0 < dep[z]! → dep[z]! ≠ 1 → par[z]! < n ∧ 0 < dep[par[z]!]! ∧
    dep[par[z]!]! + 1 = dep[z]! ∧ lab[z]! < gens.size ∧ (gens[lab[z]!]!)[par[z]!]! = z
  closed : ∀ h j', (h < a ∨ (h = a ∧ j' < j)) → h < q.size → j' < gens.size →
    0 < dep[(gens[j']!)[q[h]!]!]!
  a_le : a ≤ q.size

theorem set_self {a : Array Nat} {i v : Nat} (h : i < a.size) : (a.set! i v)[i]! = v :=
  Array.getElem!_set!_self a i v h

theorem set_ne {a : Array Nat} {i z v : Nat} (h : z ≠ i) : (a.set! i v)[z]! = a[z]! :=
  Array.getElem!_set!_ne a i z v (Ne.symm h)

theorem rinv_push {n root : Nat} {gens : Array (Array Nat)} {a j : Nat}
    {dep par lab q : Array Nat} (hI : RInv n root gens a j dep par lab q)
    (ha : a < q.size) (hj : j < gens.size) (hs : ∀ x < n, (gens[j]!)[x]! < n)
    (hy : dep[(gens[j]!)[q[a]!]!]! = 0) :
    RInv n root gens a (j + 1) (dep.set! (gens[j]!)[q[a]!]! (dep[q[a]!]! + 1))
      (par.set! (gens[j]!)[q[a]!]! q[a]!) (lab.set! (gens[j]!)[q[a]!]! j)
      (q.push (gens[j]!)[q[a]!]!) := by
  have hxn := (hI.qmem a ha).1
  have hxd := (hI.qmem a ha).2
  have hyn := hs _ hxn
  set x := q[a]! with hxdef
  set y := (gens[j]!)[x]! with hydef
  have hyx : x ≠ y := fun e => by
    rw [← e] at hy
    omega
  have dep_y : (dep.set! y (dep[x]! + 1))[y]! = dep[x]! + 1 := set_self (by rw [hI.dep_size]; exact hyn)
  have dep_ne : ∀ z, z ≠ y → (dep.set! y (dep[x]! + 1))[z]! = dep[z]! := fun z hz => set_ne hz
  have par_y : (par.set! y x)[y]! = x := set_self (by rw [hI.par_size]; exact hyn)
  have par_ne : ∀ z, z ≠ y → (par.set! y x)[z]! = par[z]! := fun z hz => set_ne hz
  have lab_y : (lab.set! y j)[y]! = j := set_self (by rw [hI.lab_size]; exact hyn)
  have lab_ne : ∀ z, z ≠ y → (lab.set! y j)[z]! = lab[z]! := fun z hz => set_ne hz
  have absent : ∀ k < q.size, q[k]! ≠ y := fun k hk e => by
    have := (hI.qmem k hk).2
    rw [e, hy] at this
    omega
  have q_lt : ∀ k < q.size, (q.push y)[k]! = q[k]! := fun k hk => push_get_lt hk
  have q_m : (q.push y)[q.size]! = y := push_get_eq rfl
  have hsz : (q.push y).size = q.size + 1 := by simp
  have hle : q.size + 1 ≤ n := succ_le_of_inj (f := fun k => q[k]!) (fun k hk k' hk' e =>
    hI.qinj k hk k' hk' e) (fun k hk => (hI.qmem k hk).1) absent hyn
  have hroot_ne : root ≠ y := fun e => by
    rw [← e, hI.root_one] at hy
    omega
  refine ⟨by rw [Array.size_set!, hI.dep_size], by rw [Array.size_set!, hI.par_size],
    by rw [Array.size_set!, hI.lab_size], by omega, by rw [q_lt 0 hI.q_pos]; exact hI.q_zero,
    by omega, ?_, ?_, ?_, by rw [dep_ne _ hroot_ne]; exact hI.root_one, ?_, ?_, ?_, by omega⟩
  · intro k hk
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [q_lt k hk, dep_ne _ (absent k hk)]
      exact hI.qmem k hk
    · rw [q_m, dep_y]
      exact ⟨hyn, by omega⟩
  · intro z hz hd
    by_cases hzy : z = y
    · exact ⟨q.size, by rw [hsz]; omega, by rw [q_m, hzy]⟩
    · rw [dep_ne _ hzy] at hd
      obtain ⟨k, hk, e⟩ := hI.qall z hz hd
      exact ⟨k, by rw [hsz]; omega, by rw [q_lt k hk, e]⟩
  · intro k hk k' hk' e
    rw [hsz] at hk hk'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · rw [q_lt k hk, q_lt k' hk'] at e
      exact hI.qinj k hk k' hk' e
    · rw [q_lt k hk, q_m] at e
      exact absurd e (absent k hk)
    · rw [q_m, q_lt k' hk'] at e
      exact absurd e.symm (absent k' hk')
    · rfl
  · intro z hz h1
    by_cases hzy : z = y
    · rw [hzy, dep_y] at h1
      omega
    · rw [dep_ne _ hzy] at h1
      exact hI.one z hz h1
  · intro z hz hd h1
    by_cases hzy : z = y
    · subst hzy
      rw [dep_y] at h1 hd ⊢
      rw [par_y, lab_y, dep_ne _ hyx]
      exact ⟨hxn, hxd, rfl, hj, rfl⟩
    · rw [dep_ne _ hzy] at hd h1 ⊢
      rw [par_ne _ hzy, lab_ne _ hzy]
      obtain ⟨e1, e2, e3, e4, e5⟩ := hI.edge z hz hd h1
      have hpy : par[z]! ≠ y := fun e => by rw [e, hy] at e2; omega
      rw [dep_ne _ hpy]
      exact ⟨e1, e2, e3, e4, e5⟩
  · intro h j' hh hq hj'
    rw [hsz] at hq
    have hha : h ≤ a := by omega
    rw [q_lt h (by omega)]
    by_cases hold : h < a ∨ (h = a ∧ j' < j)
    · have c := hI.closed h j' hold (by omega) hj'
      by_cases hzy : (gens[j']!)[q[h]!]! = y
      · rw [hzy, dep_y]
        omega
      · rw [dep_ne _ hzy]
        exact c
    · have e1 : h = a := by omega
      have e2 : j' = j := by omega
      rw [e1, e2, ← hxdef, ← hydef, dep_y]
      omega

theorem rinv_skip {n root : Nat} {gens : Array (Array Nat)} {a j : Nat}
    {dep par lab q : Array Nat} (hI : RInv n root gens a j dep par lab q)
    (hy : dep[(gens[j]!)[q[a]!]!]! ≠ 0) : RInv n root gens a (j + 1) dep par lab q := by
  refine ⟨hI.dep_size, hI.par_size, hI.lab_size, hI.q_pos, hI.q_zero, hI.q_le, hI.qmem, hI.qall,
    hI.qinj, hI.root_one, hI.one, hI.edge, fun h j' hh hq hj' => ?_, hI.a_le⟩
  by_cases hold : h < a ∨ (h = a ∧ j' < j)
  · exact hI.closed h j' hold hq hj'
  · have e1 : h = a := by omega
    have e2 : j' = j := by omega
    rw [e1, e2]
    omega

theorem rinv_next {n root : Nat} {gens : Array (Array Nat)} {a : Nat}
    {dep par lab q : Array Nat} (hI : RInv n root gens a gens.size dep par lab q)
    (ha : a < q.size) : RInv n root gens (a + 1) 0 dep par lab q :=
  ⟨hI.dep_size, hI.par_size, hI.lab_size, hI.q_pos, hI.q_zero, hI.q_le, hI.qmem, hI.qall,
    hI.qinj, hI.root_one, hI.one, hI.edge,
    fun h j' hh hq hj' => hI.closed h j' (by omega) hq hj', by omega⟩

theorem rinv_init {n root : Nat} {gens : Array (Array Nat)} (hr : root < n) :
    RInv n root gens 0 0 ((Array.replicate n 0).set! root 1) (Array.replicate n 0)
      (Array.replicate n 0) #[root] := by
  have d_root : ((Array.replicate n 0).set! root 1)[root]! = 1 := set_self (by simpa using hr)
  have d_ne : ∀ z < n, z ≠ root → ((Array.replicate n 0).set! root 1)[z]! = 0 := fun z hz hne => by
    rw [set_ne hne, getElem!_pos _ z (by simpa using hz), Array.getElem_replicate]
  have t0 : (#[root] : Array Nat)[0]! = root := rfl
  refine ⟨by simp, by simp, by simp, by simp, t0, by simp; omega, fun k hk => ?_, fun z hz hd => ?_,
    fun k hk k' hk' _ => ?_, d_root, fun z hz h1 => ?_, fun z hz hd h1 => ?_,
    fun h j' hh _ _ => ?_, by simp⟩
  · have : k = 0 := by simp at hk; omega
    subst this
    rw [t0, d_root]
    exact ⟨hr, by omega⟩
  · by_cases hzr : z = root
    · exact ⟨0, by simp, by rw [t0, hzr]⟩
    · rw [d_ne z hz hzr] at hd
      omega
  · simp at hk hk'
    omega
  · by_cases hzr : z = root
    · exact hzr
    · rw [d_ne z hz hzr] at h1
      omega
  · by_cases hzr : z = root
    · subst hzr
      exact absurd d_root h1
    · rw [d_ne z hz hzr] at hd
      omega
  · omega

theorem recFacts_of_rinv {n root : Nat} {gens : Array (Array Nat)} {a : Nat}
    {dep par lab q : Array Nat} (hI : RInv n root gens a 0 dep par lab q) (ha : q.size ≤ a) :
    RecFacts n root gens dep par lab where
  root_pos := by rw [hI.root_one]; omega
  one := hI.one
  edge := hI.edge
  closed := fun z hz hd j hj => by
    obtain ⟨k, hk, rfl⟩ := hI.qall z hz hd
    exact hI.closed k j (Or.inl (by omega)) hk hj

theorem recFacts_of_st {n root : Nat} {gens : Array (Array Nat)}
    {st : Array Nat × Array Nat × Array Nat × Array Nat}
    (h : ∃ a, st.2.2.2.size ≤ a ∧ RInv n root gens a 0 st.1 st.2.1 st.2.2.1 st.2.2.2) :
    RecFacts n root gens st.1 st.2.1 st.2.2.1 := by
  obtain ⟨a, ha, hI⟩ := h
  exact recFacts_of_rinv hI ha

theorem stepP_yield_four {β : Type} {I : Nat → β × β × β × β → Prop} {Q : β × β × β × β → Prop}
    {a : Nat} {X : β × β × β × β} (h : I (a + 1) X) :
    StepP I Q a (.yield (X.1, X.2.1, X.2.2.1, X.2.2.2)) := h

theorem recFacts_orbitRecord {n root : Nat} {gens : Array (Array Nat)} (hr : root < n)
    (hs : ∀ j < gens.size, ∀ x < n, (gens[j]!)[x]! < n) :
    RecFacts n root gens (orbitRecord n root gens).1 (orbitRecord n root gens).2.1
      (orbitRecord n root gens).2.2 := by
  unfold orbitRecord
  simp only [Id.run_bind, Id.run_pure]
  refine recFacts_of_st (forIn_range_idx n _ _
        (fun a (st : Array Nat × Array Nat × Array Nat × Array Nat) =>
          RInv n root gens a 0 st.1 st.2.1 st.2.2.1 st.2.2.2)
        (fun st => ∃ a, st.2.2.2.size ≤ a ∧ RInv n root gens a 0 st.1 st.2.1 st.2.2.1 st.2.2.2)
        (rinv_init hr) ?_ (fun b hb => ⟨n, hb.q_le, hb⟩))
  · intro a _ b hb
    split
    · rename_i hab
      simp only [Id.run_bind, Id.run_pure]
      refine stepP_yield_four (forIn_range_idx gens.size _ _
        (fun j (st : Array Nat × Array Nat × Array Nat × Array Nat) =>
          RInv n root gens a j st.1 st.2.1 st.2.2.1 st.2.2.2 ∧ a < st.2.2.2.size ∧
            st.2.2.2[a]! = b.2.2.2[a]!)
        (fun st => RInv n root gens (a + 1) 0 st.1 st.2.1 st.2.2.1 st.2.2.2)
        ⟨hb, hab, rfl⟩ ?_ (fun st hst => rinv_next hst.1 hst.2.1))
      intro j hj st hst
      obtain ⟨hI, ha, hx⟩ := hst
      split
      · rename_i hy
        dsimp only [StepP]
        rw [← hx]
        rw [← hx, beq_iff_eq] at hy
        refine ⟨rinv_push hI ha hj (hs j hj) hy, by simp; omega, ?_⟩
        rw [push_get_lt ha]
      · rename_i hy
        dsimp only [StepP]
        rw [← hx, beq_iff_eq] at hy
        exact ⟨rinv_skip hI hy, ha, hx⟩
    · rename_i hab
      exact ⟨a, Nat.le_of_not_lt hab, hb⟩

structure LInv (n : Nat) (orbs : Array (Array Nat)) (t₀ k₀ : Nat) (lab ps : Array Nat) :
    Prop where
  lab_size : lab.size = n
  ps_size : ps.size = n
  done : ∀ t < orbs.size, ∀ k < (orbs[t]!).size, (t < t₀ ∨ (t = t₀ ∧ k < k₀)) →
    lab[(orbs[t]!)[k]!]! = t ∧ ps[(orbs[t]!)[k]!]! = k

theorem stepP_yield_two {β : Type} {I : Nat → β × β → Prop} {Q : β × β → Prop}
    {a : Nat} {X : β × β} (h : I (a + 1) X) : StepP I Q a (.yield (X.1, X.2)) := h

theorem labels_orbitLabel {n : Nat} {orbs : Array (Array Nat)}
    (hlt : ∀ t < orbs.size, ∀ k < (orbs[t]!).size, (orbs[t]!)[k]! < n)
    (hinj : ∀ t < orbs.size, ∀ k < (orbs[t]!).size, ∀ t' < orbs.size, ∀ k' < (orbs[t']!).size,
      (orbs[t]!)[k]! = (orbs[t']!)[k']! → t = t' ∧ k = k') :
    ∀ t < orbs.size, ∀ k < (orbs[t]!).size,
      (orbitLabel n orbs).1[(orbs[t]!)[k]!]! = t ∧ (orbitLabel n orbs).2[(orbs[t]!)[k]!]! = k := by
  have key : LInv n orbs orbs.size 0 (orbitLabel n orbs).1 (orbitLabel n orbs).2 := by
    unfold orbitLabel
    simp only [Id.run_bind, Id.run_pure]
    refine forIn_range_idx orbs.size _ _
      (fun t (st : Array Nat × Array Nat) => LInv n orbs t 0 st.1 st.2)
      (fun st => LInv n orbs orbs.size 0 st.1 st.2) ?_ ?_ (fun b hb => hb)
    · exact ⟨by simp, by simp, fun t _ k _ h => by omega⟩
    · intro t ht b hb
      simp only [Id.run_bind, Id.run_pure]
      refine stepP_yield_two (forIn_range_idx (orbs[t]!).size _ _
        (fun k (st : Array Nat × Array Nat) => LInv n orbs t k st.1 st.2)
        (fun st => LInv n orbs (t + 1) 0 st.1 st.2) hb ?_ ?_)
      · intro k hk st hst
        dsimp only [StepP]
        have hy := hlt t ht k hk
        refine ⟨by rw [Array.size_set!, hst.lab_size], by rw [Array.size_set!, hst.ps_size],
          fun t' ht' k' hk' hold => ?_⟩
        by_cases e : (orbs[t']!)[k']! = (orbs[t]!)[k]!
        · obtain ⟨rfl, rfl⟩ := hinj t' ht' k' hk' t ht k hk e
          rw [set_self (by rw [hst.lab_size]; exact hy), set_self (by rw [hst.ps_size]; exact hy)]
          exact ⟨rfl, rfl⟩
        · rw [set_ne e, set_ne e]
          refine hst.done t' ht' k' hk' ?_
          rcases hold with h1 | ⟨h1, h2⟩
          · exact Or.inl h1
          · subst h1
            have : k' ≠ k := fun e' => e (by rw [e'])
            exact Or.inr ⟨rfl, by omega⟩
      · intro st hst
        refine ⟨hst.lab_size, hst.ps_size, fun t' ht' k' hk' hold => hst.done t' ht' k' hk' ?_⟩
        rcases hold with h1 | ⟨_, h2⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, hk'⟩
        · omega
  intro t ht k hk
  exact key.done t ht k hk (Or.inl ht)

end CFSG.KS.Co2Stab

end
