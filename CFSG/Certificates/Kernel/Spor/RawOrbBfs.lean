module

public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.Raw.Orb

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.KS.Raw

@[expose] def StepP {β : Type} (I : Nat → β → Prop) (Q : β → Prop) (a : Nat) : ForInStep β → Prop
  | .yield b => I (a + 1) b
  | .done b => Q b

theorem forIn_list_idx {β : Type} (f : Nat → β → Id (ForInStep β)) (I : Nat → β → Prop)
    (Q : β → Prop) : ∀ (k s : Nat) (init : β), I s init →
    (∀ a, s ≤ a → a < s + k → ∀ b, I a b → StepP I Q a (Id.run (f a b))) →
    (∀ b, I (s + k) b → Q b) → Q (Id.run (forIn (List.range' s k) init f)) := by
  intro k
  induction k with
  | zero =>
    intro s init h0 _ hQ
    exact hQ init (by simpa using h0)
  | succ k ih =>
    intro s init h0 hf hQ
    rw [List.range'_succ, List.forIn_cons]
    have h1 := hf s le_rfl (by omega) init h0
    cases e : f s init with
    | done b =>
      rw [e] at h1
      exact h1
    | yield b =>
      rw [e] at h1
      exact ih (s + 1) b h1 (fun a ha1 ha2 => hf a (by omega) (by omega))
        (fun b hb => hQ b (by rwa [show s + 1 + k = s + (k + 1) by omega] at hb))

theorem forIn_range_idx {β : Type} (n : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (I : Nat → β → Prop) (Q : β → Prop) (h0 : I 0 init)
    (hf : ∀ a < n, ∀ b, I a b → StepP I Q a (Id.run (f a b))) (hQ : ∀ b, I n b → Q b) :
    Q (Id.run (forIn [0:n] init f)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have e : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  simp only [e]
  exact forIn_list_idx f I Q n 0 init h0 (fun a _ ha => hf a (by omega))
    (fun b hb => hQ b (by simpa using hb))

theorem lexLt_iff {a b c d : Nat} : lexLt a b c d = true ↔ a < c ∨ (a = c ∧ b < d) := by
  simp [lexLt]

theorem lexLt_false_of {a b c d : Nat} (h : lexLt a b c d = true) : lexLt c d a b = false := by
  rw [lexLt_iff] at h
  cases e : lexLt c d a b
  · rfl
  · rw [lexLt_iff] at e
    omega

structure Inv (n root : Nat) (steps : Array (Array Nat)) (a j : Nat)
    (pos pts par lab : Array Nat) : Prop where
  pos_size : pos.size = n
  pts_pos : 0 < pts.size
  root : pts[0]! = root
  par_size : par.size = pts.size
  lab_size : lab.size = pts.size
  le : pts.size ≤ n
  pt : ∀ k < pts.size, pts[k]! < n ∧ pos[pts[k]!]! = k
  posz : ∀ z < n, pos[z]! = n ∨ (pos[z]! < pts.size ∧ pts[pos[z]!]! = z)
  edge : ∀ k < pts.size, 0 < k → par[k]! < k ∧ lab[k]! < steps.size ∧
    steps[lab[k]!]![pts[par[k]!]!]! = pts[k]!
  mono : ∀ k, 0 < k → k + 1 < pts.size → lexLt par[k]! lab[k]! par[k + 1]! lab[k + 1]! = true
  front : ∀ k < pts.size, 0 < k → lexLt par[k]! lab[k]! a j = true
  closed : ∀ h j', (h < a ∨ (h = a ∧ j' < j)) → j' < steps.size →
    pos[steps[j']![pts[h]!]!]! < pts.size ∧ (pos[steps[j']![pts[h]!]!]! = 0 ∨
      lexLt h j' par[pos[steps[j']![pts[h]!]!]!]! lab[pos[steps[j']![pts[h]!]!]!]! = false)
  a_le : a ≤ pts.size

theorem succ_le_of_inj {m n y : Nat} {f : Nat → Nat} (hf : ∀ k < m, ∀ k' < m, f k = f k' → k = k')
    (hlt : ∀ k < m, f k < n) (hne : ∀ k < m, f k ≠ y) (hy : y < n) : m + 1 ≤ n := by
  have hsub : (Finset.range m).image f ⊆ (Finset.range n).erase y := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    rw [Finset.mem_range] at hk
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨hne k hk, hlt k hk⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun k hk k' hk' e => hf k (by simpa using hk) k'
    (by simpa using hk') e), Finset.card_range, Finset.card_erase_of_mem (by simpa using hy),
    Finset.card_range] at hc
  omega

theorem lexLt_succ {p l a j : Nat} (h : lexLt p l a j = true) : lexLt p l a (j + 1) = true := by
  rw [lexLt_iff] at h ⊢
  omega

theorem inv_push {n root : Nat} {steps : Array (Array Nat)} {a j : Nat}
    {pos pts par lab : Array Nat} (hI : Inv n root steps a j pos pts par lab)
    (ha : a < pts.size) (hj : j < steps.size) (hs : ∀ x < n, steps[j]![x]! < n)
    (hy : pos[steps[j]![pts[a]!]!]! = n) :
    Inv n root steps a (j + 1) (pos.set! steps[j]![pts[a]!]! pts.size)
      (pts.push steps[j]![pts[a]!]!) (par.push a) (lab.push j) := by
  set y := steps[j]![pts[a]!]! with hydef
  set m := pts.size with hm
  have hyn : y < n := hs _ (hI.pt a ha).1
  have hmn := hI.le
  have pos_y : (pos.set! y m)[y]! = m :=
    Array.getElem!_set!_self pos y m (by rw [hI.pos_size]; exact hyn)
  have pos_ne : ∀ z, z ≠ y → (pos.set! y m)[z]! = pos[z]! := fun z hz =>
    Array.getElem!_set!_ne pos y z m (Ne.symm hz)
  have absent : ∀ k < m, pts[k]! ≠ y := by
    intro k hk e
    have := (hI.pt k hk).2
    rw [e, hy] at this
    omega
  have pts_lt : ∀ k < m, (pts.push y)[k]! = pts[k]! := fun k hk => push_get_lt hk
  have pts_m : (pts.push y)[m]! = y := push_get_eq rfl
  have par_lt : ∀ k < m, (par.push a)[k]! = par[k]! := fun k hk =>
    push_get_lt (by rw [hI.par_size]; exact hk)
  have par_m : (par.push a)[m]! = a := push_get_eq hI.par_size.symm
  have lab_lt : ∀ k < m, (lab.push j)[k]! = lab[k]! := fun k hk =>
    push_get_lt (by rw [hI.lab_size]; exact hk)
  have lab_m : (lab.push j)[m]! = j := push_get_eq hI.lab_size.symm
  have hsz : (pts.push y).size = m + 1 := by simp [hm]
  refine ⟨by rw [Array.size_set!, hI.pos_size], by omega, ?_, by simp [hI.par_size],
    by simp [hI.lab_size], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [pts_lt 0 hI.pts_pos]
    exact hI.root
  · rw [hsz]
    exact succ_le_of_inj (f := fun k => pts[k]!)
      (fun k hk k' hk' e => by rw [← (hI.pt k hk).2, ← (hI.pt k' hk').2]; exact congrArg _ e)
      (fun k hk => (hI.pt k hk).1) absent hyn
  · intro k hk
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [pts_lt k hk, pos_ne _ (absent k hk)]
      exact hI.pt k hk
    · rw [pts_m, pos_y]
      exact ⟨hyn, rfl⟩
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      rw [pos_y, hsz, pts_m]
      exact Or.inr ⟨by omega, rfl⟩
    · rw [pos_ne z hzy, hsz]
      rcases hI.posz z hz with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by rw [pts_lt _ h1]; exact h2⟩
  · intro k hk hk0
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨e1, e2, e3⟩ := hI.edge k hk hk0
      rw [par_lt k hk, lab_lt k hk, pts_lt k hk, pts_lt _ (by omega)]
      exact ⟨e1, e2, e3⟩
    · rw [par_m, lab_m, pts_m, pts_lt a ha]
      exact ⟨ha, hj, rfl⟩
  · intro k hk0 hk1
    rw [hsz] at hk1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk1 with hk1 | hk1
    · rw [par_lt k (by omega), lab_lt k (by omega), par_lt (k + 1) hk1, lab_lt (k + 1) hk1]
      exact hI.mono k hk0 hk1
    · rw [par_lt k (by omega), lab_lt k (by omega), hk1, par_m, lab_m]
      exact hI.front k (by omega) hk0
  · intro k hk hk0
    rw [hsz] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [par_lt k hk, lab_lt k hk]
      exact lexLt_succ (hI.front k hk hk0)
    · rw [par_m, lab_m, lexLt_iff]
      omega
  · intro h j' hh hj'
    have hha : h ≤ a := by omega
    rw [pts_lt h (by omega), hsz]
    by_cases hold : h < a ∨ (h = a ∧ j' < j)
    · obtain ⟨c1, c2⟩ := hI.closed h j' hold hj'
      have hzy : steps[j']![pts[h]!]! ≠ y := fun e => by
        rw [e, hy] at c1
        omega
      rw [pos_ne _ hzy, par_lt _ c1, lab_lt _ c1]
      exact ⟨by omega, c2⟩
    · have e1 : h = a := by omega
      have e2 : j' = j := by omega
      rw [e1, e2, ← hydef, pos_y, par_m, lab_m]
      refine ⟨by omega, Or.inr ?_⟩
      simp [lexLt]

theorem inv_skip {n root : Nat} {steps : Array (Array Nat)} {a j : Nat}
    {pos pts par lab : Array Nat} (hI : Inv n root steps a j pos pts par lab)
    (hyn : steps[j]![pts[a]!]! < n) (hy : pos[steps[j]![pts[a]!]!]! ≠ n) :
    Inv n root steps a (j + 1) pos pts par lab := by
  refine ⟨hI.pos_size, hI.pts_pos, hI.root, hI.par_size, hI.lab_size, hI.le, hI.pt, hI.posz,
    hI.edge, hI.mono, fun k hk hk0 => lexLt_succ (hI.front k hk hk0), ?_, hI.a_le⟩
  intro h j' hh hj'
  by_cases hold : h < a ∨ (h = a ∧ j' < j)
  · exact hI.closed h j' hold hj'
  · have e1 : h = a := by omega
    have e2 : j' = j := by omega
    rw [e1, e2]
    rcases hI.posz _ hyn with e | ⟨c1, _⟩
    · exact absurd e hy
    · refine ⟨c1, ?_⟩
      rcases Nat.eq_zero_or_pos (pos[steps[j]![pts[a]!]!]!) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (lexLt_false_of (hI.front _ c1 h0))

theorem inv_next {n root : Nat} {steps : Array (Array Nat)} {a : Nat}
    {pos pts par lab : Array Nat} (hI : Inv n root steps a steps.size pos pts par lab)
    (ha : a < pts.size) : Inv n root steps (a + 1) 0 pos pts par lab := by
  refine ⟨hI.pos_size, hI.pts_pos, hI.root, hI.par_size, hI.lab_size, hI.le, hI.pt, hI.posz,
    hI.edge, hI.mono, fun k hk hk0 => ?_, fun h j' hh hj' => hI.closed h j' (by omega) hj',
    by omega⟩
  have := hI.front k hk hk0
  rw [lexLt_iff] at this ⊢
  omega

theorem replicate_get {n z : Nat} (hz : z < n) : (Array.replicate n n)[z]! = n := by
  rw [getElem!_pos _ z (by simpa using hz), Array.getElem_replicate]

theorem inv_init {n root : Nat} {steps : Array (Array Nat)} (hr : root < n) :
    Inv n root steps 0 0 ((Array.replicate n n).set! root 0) #[root] #[0] #[0] := by
  have p_root : ((Array.replicate n n).set! root 0)[root]! = 0 :=
    Array.getElem!_set!_self _ _ _ (by simpa using hr)
  have p_ne : ∀ z < n, z ≠ root → ((Array.replicate n n).set! root 0)[z]! = n := fun z hz hne => by
    rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne), replicate_get hz]
  have t0 : (#[root] : Array Nat)[0]! = root := rfl
  refine ⟨by simp, by simp, t0, rfl, rfl, by simp; omega, fun k hk => ?_, fun z hz => ?_,
    fun k hk hk0 => ?_, fun k hk0 hk1 => ?_, fun k hk hk0 => ?_, fun h j' hh _ => ?_, by simp⟩
  · simp only [List.size_toArray, List.length_cons, List.length_nil] at hk
    have : k = 0 := by omega
    subst this
    rw [t0, p_root]
    exact ⟨hr, rfl⟩
  · by_cases hzr : z = root
    · subst hzr
      rw [p_root]
      exact Or.inr ⟨by simp, t0⟩
    · exact Or.inl (p_ne z hz hzr)
  · simp at hk
    omega
  · simp at hk1
  · simp at hk
    omega
  · omega

theorem levelOKT_of_inv {n root : Nat} {steps : Array (Array Nat)} {a : Nat}
    {pos pts par lab : Array Nat} (hI : Inv n root steps a 0 pos pts par lab) (ha : pts.size ≤ a)
    (tr tri : Array (Array Nat)) :
    levelOKT n root steps ⟨pts, pos, par, lab, tr, tri⟩ = true := by
  unfold levelOKT
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨hI.pts_pos, hI.le⟩, hI.root⟩, fun k hk => ?_⟩, fun z hz => ?_⟩, fun k hk => ?_⟩,
    fun k hk => ?_⟩, fun h hh j hj => ?_⟩
  · exact hI.pt k hk
  · simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
    rcases hI.posz z hz with e | ⟨_, e2⟩
    · left
      rw [e]
      exact Nat.not_lt.2 hI.le
    · exact Or.inr e2
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inl h0
    · obtain ⟨e1, e2, e3⟩ := hI.edge k hk h0
      exact Or.inr ⟨⟨e1, e2⟩, e3⟩
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inl (Or.inl h0)
    · by_cases hk1 : k + 1 < pts.size
      · exact Or.inr (hI.mono k h0 hk1)
      · exact Or.inl (Or.inr hk1)
  · obtain ⟨c1, c2⟩ := hI.closed h j (Or.inl (by omega)) hj
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact ⟨c1, c2⟩

theorem levelOKT_of_st {n root : Nat} {steps : Array (Array Nat)}
    {st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat)}
    (h : ∃ a, st.2.1.size ≤ a ∧ Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1) :
    levelOKT n root steps
      ⟨st.2.1, st.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, st.2.2.2.2.map (invCand n)⟩ = true := by
  obtain ⟨a, ha, hI⟩ := h
  exact levelOKT_of_inv hI ha _ _

theorem stepP_yield_of {β γ : Type} {I : Nat → β × β × β × β × γ → Prop} {Q : β × β × β × β × γ → Prop}
    {a : Nat} {X : β × β × β × β × γ} (h : I (a + 1) X) :
    StepP I Q a (.yield (X.1, X.2.1, X.2.2.1, X.2.2.2.1, X.2.2.2.2)) := h

theorem levelOKT_bfs {n root : Nat} {steps : Array (Array Nat)} (hr : root < n)
    (hs : ∀ j < steps.size, ∀ x < n, steps[j]![x]! < n) :
    levelOKT n root steps (CFSG.Monster.B.Co2.Native.bfs n root steps) = true := by
  unfold CFSG.Monster.B.Co2.Native.bfs
  simp only [Id.run_bind, Id.run_pure]
  refine levelOKT_of_st (forIn_range_idx n _ _
        (fun a (st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat)) =>
          Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        (fun st => ∃ a, st.2.1.size ≤ a ∧ Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        ?_ ?_ (fun b hb => ⟨n, hb.le, hb⟩))
  · exact inv_init hr
  · intro a _ b hb
    split
    · rename_i hab
      simp only [Id.run_bind, Id.run_pure]
      refine stepP_yield_of (forIn_range_idx steps.size _ _
        (fun j (st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat)) =>
          Inv n root steps a j st.1 st.2.1 st.2.2.1 st.2.2.2.1 ∧ a < st.2.1.size ∧
            st.2.1[a]! = b.2.1[a]!)
        (fun st => Inv n root steps (a + 1) 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        ⟨hb, hab, rfl⟩ ?_ (fun st hst => inv_next hst.1 hst.2.1))
      intro j hj st hst
      obtain ⟨hI, ha, hx⟩ := hst
      have hxn : st.2.1[a]! < n := (hI.pt a ha).1
      split
      · rename_i hy
        dsimp only [StepP]
        rw [← hx]
        rw [← hx, beq_iff_eq] at hy
        refine ⟨inv_push hI ha hj (hs j hj) hy, by simp; omega, ?_⟩
        rw [push_get_lt ha]
      · rename_i hy
        dsimp only [StepP]
        rw [← hx, beq_iff_eq] at hy
        exact ⟨inv_skip hI (hs j hj _ hxn) hy, ha, hx⟩
    · rename_i hab
      exact ⟨a, Nat.le_of_not_lt hab, hb⟩

end CFSG.KS.Raw.Orb

end
