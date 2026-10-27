module

public import CFSG.Sporadic.Schreier.ONCompactSpec

public section

namespace CFSG.KS.CBF

open CFSG.ONSchreier.Native CFSG.ONSchreier

private abbrev CSt := Array Nat × Array Nat × Array Nat × Array Nat

private def cInner (n : Nat) (st : Array (Array Nat)) (x h : Nat) (j : Nat) (s : CSt) :
    Id (ForInStep CSt) :=
  if (s.1[(st[j]!)[x]!]! == n) = true then
    pure (.yield (s.1.set! (st[j]!)[x]! s.2.1.size, s.2.1.push (st[j]!)[x]!, s.2.2.1.push h,
      s.2.2.2.push j))
  else pure (.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def cOuter (n : Nat) (st : Array (Array Nat)) (h : Nat) (s : CSt) : Id (ForInStep CSt) :=
  if h < s.2.1.size then do
    let s' ← forIn [0:st.size] (s.1, s.2.1, s.2.2.1, s.2.2.2) (cInner n st s.2.1[h]! h)
    pure (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2))
  else pure (.done (s.1, s.2.1, s.2.2.1, s.2.2.2))

private theorem cbfs_eq (n root : Nat) (st : Array (Array Nat)) :
    cbfs n root st =
      (let s := (forIn [0:n] ((Array.replicate n n).set! root 0, #[root], #[0], #[0])
        (cOuter n st) : Id CSt)
      ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩) := rfl

private theorem forIn_inv {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_inv R E f hf k (a + 1) b' (by omega) hR

private theorem forIn_brk {β : Type} (P : Nat → β → Prop) (Q : β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ h b, h < E → P h b →
      (∃ b', f h b = pure (.yield b') ∧ P (h + 1) b') ∨ (∃ b', f h b = pure (.done b') ∧ Q b'))
    (hE : ∀ b, P E b → Q b) :
    ∀ k a (init : β), a + k = E → P a init → Q (forIn (List.range' a k) init f)
  | 0, a, init, hk, h => by
    have e : a = E := hk
    subst e
    exact hE init h
  | k + 1, a, init, hk, h => by
    rcases hf a init (by omega) h with ⟨b', hb, hP⟩ | ⟨b', hb, hQ⟩
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact forIn_brk P Q E f hf hE k (a + 1) b' (by omega) hP
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact hQ

private theorem set_getC {a : Array Nat} {i j : Nat} {v : Nat} (hi : i < a.size) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [getElem!_pos _ j hj', getElem!_pos a j hj]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]
  · have hj' : ¬ j < (a.set! i v).size := by simpa using hj
    have hij : j ≠ i := by omega
    rw [getElem!_neg _ j hj', getElem!_neg a j hj, ite_eq_right hij]

private theorem push_lt {a : Array Nat} {v k : Nat} (hk : k < a.size) : (a.push v)[k]! = a[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, getElem!_pos a k hk]

private theorem push_eq {a : Array Nat} {v : Nat} : (a.push v)[a.size]! = v := by
  rw [getElem!_pos _ a.size (by simp), Array.getElem_push_eq]

private theorem le_of_linv {M n : Nat} {f g : Nat → Nat} (hf : ∀ k < M, f k < n)
    (hg : ∀ k < M, g (f k) = k) : M ≤ n := by
  have h := Finset.card_le_card_of_injOn f (s := Finset.range M) (t := Finset.range n)
    (fun k hk => by simpa using hf k (by simpa using hk))
    (fun a ha b hb e => by
      rw [← hg a (by simpa using ha), ← hg b (by simpa using hb)]
      exact congrArg g e)
  simpa using h

@[expose] def Lx (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

theorem plexLt_iff (a b c d : Nat) : plexLt a b c d = true ↔ Lx a b c d := by
  simp [plexLt, Lx]

private structure BInv (n root : Nat) (st : Array (Array Nat)) (h j : Nat)
    (pos pts par lab : Array Nat) : Prop where
  pos_size : pos.size = n
  par_size : par.size = pts.size
  lab_size : lab.size = pts.size
  pos0 : 0 < pts.size
  le : pts.size ≤ n
  root : pts[0]! = root
  pts_lt : ∀ k < pts.size, pts[k]! < n
  pos_pts : ∀ k < pts.size, pos[pts[k]!]! = k
  pos_z : ∀ z < n, pos[z]! = n ∨ (pos[z]! < pts.size ∧ pts[pos[z]!]! = z)
  par_lt : ∀ k < pts.size, 0 < k → par[k]! < k
  lab_lt : ∀ k < pts.size, 0 < k → lab[k]! < st.size
  edge : ∀ k < pts.size, 0 < k → (st[lab[k]!]!)[pts[par[k]!]!]! = pts[k]!
  done : ∀ k < pts.size, 0 < k → Lx par[k]! lab[k]! h j
  mono : ∀ k < pts.size, 0 < k → k + 1 < pts.size → Lx par[k]! lab[k]! par[k + 1]! lab[k + 1]!
  closed : ∀ h' < pts.size, ∀ j' < st.size, Lx h' j' h j →
    pos[(st[j']!)[pts[h']!]!]! < pts.size ∧
      (pos[(st[j']!)[pts[h']!]!]! = 0 ∨
        ¬ Lx h' j' par[pos[(st[j']!)[pts[h']!]!]!]! lab[pos[(st[j']!)[pts[h']!]!]!]!)

private theorem lx_succ {a b h j : Nat} (hl : Lx a b h (j + 1)) : Lx a b h j ∨ (a = h ∧ b = j) := by
  unfold Lx at *
  omega

private theorem lx_irrefl {a b c d : Nat} (h1 : Lx a b c d) : ¬ Lx c d a b := by
  unfold Lx at *
  omega

private theorem inner_step {n root : Nat} {st : Array (Array Nat)}
    (hst : ∀ j < st.size, ∀ x < n, (st[j]!)[x]! < n) {h j : Nat} {x : Nat}
    {pos pts par lab : Array Nat} (I : BInv n root st h j pos pts par lab) (hh : h < pts.size)
    (hx : pts[h]! = x) (hj : j < st.size) :
    ∃ s', cInner n st x h j (pos, pts, par, lab) = pure (.yield s') ∧
      BInv n root st h (j + 1) s'.1 s'.2.1 s'.2.2.1 s'.2.2.2 ∧ s'.2.1[h]! = x ∧
      h < s'.2.1.size := by
  have hxn : x < n := hx ▸ I.pts_lt h hh
  have hyn : (st[j]!)[x]! < n := hst j hj x hxn
  unfold cInner
  simp only
  set y := (st[j]!)[x]! with hy
  by_cases hpy : pos[y]! = n
  · rw [ite_eq_left (by simp [hpy])]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only
      set m := pts.size with hm
      have hsz : (pts.push y).size = m + 1 := by simp [hm]
      have hpsz : y < pos.size := by rw [I.pos_size]; exact hyn
      have hP : ∀ k < m + 1, (pts.push y)[k]! = if k < m then pts[k]! else y := fun k hk => by
        by_cases hk : k < m
        · rw [ite_eq_left hk, push_lt hk]
        · rw [ite_eq_right hk, show k = pts.size by omega, push_eq]
      have hR : ∀ k < m + 1, (par.push h)[k]! = if k < m then par[k]! else h := fun k hk => by
        by_cases hk : k < m
        · rw [ite_eq_left hk, push_lt (by rw [I.par_size]; exact hk)]
        · rw [ite_eq_right hk, show k = par.size by rw [I.par_size]; omega, push_eq]
      have hL : ∀ k < m + 1, (lab.push j)[k]! = if k < m then lab[k]! else j := fun k hk => by
        by_cases hk : k < m
        · rw [ite_eq_left hk, push_lt (by rw [I.lab_size]; exact hk)]
        · rw [ite_eq_right hk, show k = lab.size by rw [I.lab_size]; omega, push_eq]
      have hO : ∀ z, (pos.set! y m)[z]! = if z = y then m else pos[z]! := fun z => set_getC hpsz
      have hne : ∀ k < m, pts[k]! ≠ y := fun k hk e => by
        have := I.pos_pts k hk
        rw [e, hpy] at this
        have := I.le
        omega
      have hpts_lt : ∀ k < (pts.push y).size, (pts.push y)[k]! < n := fun k hk => by
        rw [hP k (by omega)]
        split
        · exact I.pts_lt k (by assumption)
        · exact hyn
      have hpos_pts : ∀ k < (pts.push y).size, (pos.set! y m)[(pts.push y)[k]!]! = k :=
          fun k hk => by
        rw [hP k (by omega)]
        split
        · rename_i hk'
          rw [hO, ite_eq_right (hne k hk'), I.pos_pts k hk']
        · rw [hO, ite_eq_left rfl]
          omega
      refine ⟨by simp [I.pos_size], by simp [I.par_size], by simp [I.lab_size], by omega,
        le_of_linv hpts_lt hpos_pts, by rw [hP 0 (by omega), ite_eq_left I.pos0, I.root], hpts_lt,
        hpos_pts, fun z hz => ?_, fun k hk hk0 => ?_, fun k hk hk0 => ?_, fun k hk hk0 => ?_,
        fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_, fun h' hh' j' hj' hl => ?_⟩
      · rw [hO]
        by_cases hzy : z = y
        · rw [ite_eq_left hzy, hP m (by omega), ite_eq_right (by omega), hzy]
          exact Or.inr ⟨by omega, rfl⟩
        · rw [ite_eq_right hzy]
          rcases I.pos_z z hz with e | ⟨e1, e2⟩
          · exact Or.inl e
          · refine Or.inr ⟨by omega, ?_⟩
            rw [hP _ (by omega), ite_eq_left e1, e2]
      · rw [hR k (by omega)]
        split
        · exact I.par_lt k (by assumption) hk0
        · omega
      · rw [hL k (by omega)]
        split
        · exact I.lab_lt k (by assumption) hk0
        · exact hj
      · by_cases hk' : k < m
        · have hp := I.par_lt k hk' hk0
          rw [hL k (by omega), ite_eq_left hk', hR k (by omega), ite_eq_left hk', hP _ (by omega),
            ite_eq_left (by omega),
            hP k (by omega), ite_eq_left hk']
          exact I.edge k hk' hk0
        · rw [hL k (by omega), ite_eq_right hk', hR k (by omega), ite_eq_right hk', hP _ (by omega),
            ite_eq_left hh, hx,
            hP k (by omega), ite_eq_right hk']
      · rw [hL k (by omega), hR k (by omega)]
        split
        · have := I.done k (by assumption) hk0
          unfold Lx at *
          omega
        · unfold Lx
          omega
      · by_cases hk' : k + 1 < m
        · rw [hL k (by omega), hR k (by omega), hL _ (by omega), hR _ (by omega),
            ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hk', ite_eq_left hk']
          exact I.mono k (by omega) hk0 hk'
        · rw [hL k (by omega), hR k (by omega), hL _ (by omega), hR _ (by omega),
            ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right hk', ite_eq_right hk']
          exact I.done k (by omega) hk0
      · have hh'm : h' < m := by unfold Lx at hl; omega
        rw [hP h' (by omega), ite_eq_left hh'm]
        rcases lx_succ hl with hl | ⟨e1, e2⟩
        · obtain ⟨c1, c2⟩ := I.closed h' hh'm j' hj' hl
          have hy' : (st[j']!)[pts[h']!]! ≠ y := fun e => by rw [e, hpy] at c1; have := I.le; omega
          rw [hO, ite_eq_right hy', hR _ (by omega), hL _ (by omega), ite_eq_left c1,
            ite_eq_left c1]
          exact ⟨by omega, c2⟩
        · subst e1 e2
          rw [hx, hO, ite_eq_left rfl, hR m (by omega), hL m (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
          refine ⟨by omega, Or.inr ?_⟩
          unfold Lx
          omega
    · simp only
      rw [push_lt hh, hx]
    · simp
      omega
  · rw [ite_eq_right (by simpa using hpy)]
    refine ⟨_, rfl, ?_, hx, hh⟩
    simp only
    obtain ⟨c1, c2⟩ := (I.pos_z y hyn).resolve_left hpy
    refine ⟨I.pos_size, I.par_size, I.lab_size, I.pos0, I.le, I.root, I.pts_lt, I.pos_pts, I.pos_z,
      I.par_lt, I.lab_lt, I.edge, fun k hk hk0 => ?_, I.mono, fun h' hh' j' hj' hl => ?_⟩
    · have := I.done k hk hk0
      unfold Lx at *
      omega
    · rcases lx_succ hl with hl | ⟨e1, e2⟩
      · exact I.closed h' hh' j' hj' hl
      · subst e1 e2
        rw [hx]
        refine ⟨c1, ?_⟩
        by_cases hk0 : pos[y]! = 0
        · exact Or.inl hk0
        · exact Or.inr (lx_irrefl (I.done _ c1 (Nat.pos_of_ne_zero hk0)))

private theorem binv_next {n root : Nat} {st : Array (Array Nat)} {h : Nat}
    {pos pts par lab : Array Nat} (I : BInv n root st h st.size pos pts par lab) :
    BInv n root st (h + 1) 0 pos pts par lab := by
  refine ⟨I.pos_size, I.par_size, I.lab_size, I.pos0, I.le, I.root, I.pts_lt, I.pos_pts, I.pos_z,
    I.par_lt, I.lab_lt, I.edge, fun k hk hk0 => ?_, I.mono, fun h' hh' j' hj' hl => ?_⟩
  · have := I.done k hk hk0
    have := I.lab_lt k hk hk0
    unfold Lx at *
    omega
  · exact I.closed h' hh' j' hj' (by unfold Lx at *; omega)

private theorem facts_of_binv {n root : Nat} {st : Array (Array Nat)} {h : Nat}
    {pos pts par lab : Array Nat} (I : BInv n root st h 0 pos pts par lab) (hm : pts.size ≤ h) :
    CLevelFacts n root st ⟨pts, pos, par, lab⟩ := by
  refine ⟨I.pos0, I.le, I.root, I.pts_lt, I.pos_pts, fun z hz hzm => ?_, I.par_lt, I.lab_lt,
    I.edge, fun k hk hk0 hk1 => (plexLt_iff _ _ _ _).2 (I.mono k hk hk0 hk1),
    fun h' hh' j' hj' => ?_⟩
  · rcases I.pos_z z hz with e | ⟨-, e⟩
    · simp only at hzm
      have := I.le
      omega
    · exact e
  · obtain ⟨c1, c2⟩ := I.closed h' hh' j' hj' (Or.inl (Nat.lt_of_lt_of_le hh' hm))
    refine ⟨c1, ?_⟩
    rcases c2 with c2 | c2
    · exact Or.inl c2
    · exact Or.inr (Bool.eq_false_iff.2 fun e => c2 ((plexLt_iff _ _ _ _).1 e))

theorem cbfs_facts {n root : Nat} {st : Array (Array Nat)} (hr : root < n)
    (hst : ∀ j < st.size, ∀ x < n, (st[j]!)[x]! < n) :
    CLevelFacts n root st (cbfs n root st) := by
  rw [cbfs_eq]
  simp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hl : List.range' [0:n].start [0:n].size [0:n].step = List.range' 0 n := by
    simp [Std.Legacy.Range.size]
  rw [hl]
  refine forIn_brk (fun h s => BInv n root st h 0 s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun s : CSt => CLevelFacts n root st ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩) n (cOuter n st)
    (fun h b hn hb => ?_) (fun b hb => facts_of_binv hb hb.le) n 0 _ (Nat.zero_add n) ?_
  · obtain ⟨pos, pts, par, lab⟩ := b
    by_cases hc : h < pts.size
    · refine Or.inl ⟨_, by unfold cOuter; rw [ite_eq_left hc]; rfl, ?_⟩
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      have hl' : List.range' [0:st.size].start [0:st.size].size [0:st.size].step =
          List.range' 0 st.size := by simp [Std.Legacy.Range.size]
      rw [hl']
      have := forIn_inv (fun j (s : CSt) => BInv n root st h j s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
          s.2.1[h]! = pts[h]! ∧ h < s.2.1.size) st.size (cInner n st pts[h]! h)
        (fun j s hj ⟨I, hx, hh⟩ => by
          obtain ⟨pos', pts', par', lab'⟩ := s
          obtain ⟨s', e, I', hx', hh'⟩ := inner_step hst I hh hx hj
          exact ⟨s', e, I', hx', hh'⟩)
        st.size 0 (pos, pts, par, lab) (by omega) ⟨hb, rfl, hc⟩
      rw [Nat.zero_add] at this
      exact binv_next this.1
    · exact Or.inr ⟨_, by unfold cOuter; rw [ite_eq_right hc],
        facts_of_binv hb (Nat.le_of_not_lt hc)⟩
  · have hpsz : root < (Array.replicate n n).size := by simpa using hr
    have hO : ∀ z, ((Array.replicate n n).set! root 0)[z]! = if z = root then 0 else
        (Array.replicate n n)[z]! := fun z => set_getC hpsz
    have h1 : (#[root] : Array Nat).size = 1 := rfl
    have e0 : (#[root] : Array Nat)[0]! = root := by simp
    change BInv n root st 0 0 ((Array.replicate n n).set! root 0) #[root] #[0] #[0]
    refine ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp,
      fun k hk => ?_, fun k hk => ?_, fun z hz => ?_, fun k hk hk0 => ?_, fun k hk hk0 => ?_,
      fun k hk hk0 => ?_, fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_, fun h' hh' j' hj' hl => ?_⟩
    · have hk0 : k = 0 := by omega
      rw [hk0, e0]
      exact hr
    · have hk0 : k = 0 := by omega
      rw [hk0, e0, hO, ite_eq_left rfl]
    · rw [hO]
      by_cases hz' : z = root
      · rw [ite_eq_left hz']
        exact Or.inr ⟨by simp, by simp [hz']⟩
      · rw [ite_eq_right hz', getElem!_pos _ z (by simpa using hz), Array.getElem_replicate]
        exact Or.inl rfl
    all_goals first | omega | (unfold Lx at hl; omega)

theorem clevelOK_of_facts {n root : Nat} {steps : Array (Array Nat)} {L : CLevel}
    (F : CLevelFacts n root steps L) : clevelOK n root steps L = true := by
  simp only [clevelOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelowN_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨F.pos, F.le⟩, F.root⟩, fun k hk => ⟨F.pts_lt k hk, F.pos_pts k hk⟩⟩,
    fun z hz => ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun h hh j hj => ?_⟩
  · by_cases hq : L.pos[z]! < L.pts.size
    · simpa [hq] using F.pts_pos z hz hq
    · simp [hq]
  · by_cases hk0 : k = 0
    · simp [hk0]
    · have hp : 0 < k := Nat.pos_of_ne_zero hk0
      simpa [hk0, F.par_lt k hk hp, F.lab_lt k hk hp] using F.edge k hk hp
  · by_cases hk0 : k = 0
    · simp [hk0]
    · by_cases hk1 : k + 1 < L.pts.size
      · simp [hk1, F.mono k hk (Nat.pos_of_ne_zero hk0) hk1]
      · simp [hk1]
  · obtain ⟨c1, c2⟩ := F.closed h hh j hj
    refine ⟨c1, ?_⟩
    rcases c2 with c2 | c2
    · simp [c2]
    · simp [c2]

theorem clevelOK_cbfs {n root : Nat} {st : Array (Array Nat)} (hr : root < n)
    (hst : ∀ j < st.size, ∀ x < n, (st[j]!)[x]! < n) :
    clevelOK n root st (cbfs n root st) = true :=
  clevelOK_of_facts (cbfs_facts hr hst)

end CFSG.KS.CBF

end
