module

public import CFSG.Certificates.Kernel.M24G.IdxSound

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall

theorem drop_eq_cons {β : Type} {l : List β} {n : Nat} {y : β} {t : List β}
    (e : l.drop n = y :: t) : ∃ hn : n < l.length, l[n] = y ∧ l.drop (n + 1) = t := by
  have hn : n < l.length := by
    refine Nat.lt_of_not_le fun h => ?_
    rw [List.drop_eq_nil_of_le h] at e
    cases e
  rw [List.drop_eq_getElem_cons hn] at e
  injection e with e1 e2
  exact ⟨hn, e1, e2⟩

theorem getD_of_drop_eq_cons {l : List Nat} {n y : Nat} {t : List Nat}
    (e : l.drop n = y :: t) : n < l.length ∧ l.getD n 0 = y ∧ l.drop (n + 1) = t := by
  obtain ⟨hn, e1, e2⟩ := drop_eq_cons e
  refine ⟨hn, ?_, e2⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, e1]
  rfl

variable {α : Type} [DecidableEq α] {key : α → Nat} {pos : KTree (Nat × Nat)} {L : List α}
  {par gen : List Nat}

theorem replayStep_spec (hpos : posOK key L pos = true) (x : α) (h : Nat) :
    ∀ (ss : List (α → α)) (j : Nat) (nw : List α) (np ng : List Nat) (sz : Nat)
      (nw' : List α) (np' ng' : List Nat) (sz' : Nat),
      replayStep key pos x h ss j nw np ng sz = some (nw', np', ng', sz') →
      nw = L.drop sz → np = par.drop sz → ng = gen.drop sz →
      nw' = L.drop sz' ∧ np' = par.drop sz' ∧ ng' = gen.drop sz' ∧ sz ≤ sz' ∧
        (sz < sz' → sz' ≤ L.length ∧ sz' ≤ par.length ∧ sz' ≤ gen.length) ∧
        (∀ p, sz ≤ p → p < sz' → ∃ hp : p < L.length, par.getD p 0 = h ∧
          j ≤ gen.getD p 0 ∧ gen.getD p 0 < j + ss.length ∧
          (ss.getD (gen.getD p 0 - j) id) x = L[p]) ∧
        (∀ s ∈ ss, ∃ i, ∃ _ : i < L.length, key L[i] = key (s x))
  | [], j, nw, np, ng, sz, nw', np', ng', sz', hr, e1, e2, e3 => by
    simp only [replayStep, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    refine ⟨e1, e2, e3, Nat.le_refl _, fun h' => absurd h' (Nat.lt_irrefl _),
      fun p h1 h2 => absurd h2 (by omega), ?_⟩
    intro s hs
    cases hs
  | s :: ss, j, nw, np, ng, sz, nw', np', ng', sz', hr, e1, e2, e3 => by
    simp only [replayStep] at hr
    split at hr
    · cases hr
    · rename_i i hf
      have hcl : ∃ i, ∃ _ : i < L.length, key L[i] = key (s x) := by
        obtain ⟨hi, e⟩ := (findK_eq_some key hpos _ i).1 hf
        exact ⟨i, hi, e⟩
      split at hr
      · obtain ⟨r1, r2, r3, r4, r0, r5, r6⟩ :=
          replayStep_spec hpos x h ss (j + 1) nw np ng sz nw' np' ng' sz' hr e1 e2 e3
        refine ⟨r1, r2, r3, r4, r0, ?_, ?_⟩
        · intro p h1 h2
          obtain ⟨hp, q1, q2, q3, q4⟩ := r5 p h1 h2
          refine ⟨hp, q1, by omega, by simp only [List.length_cons]; omega, ?_⟩
          have e : gen.getD p 0 - j = (gen.getD p 0 - (j + 1)) + 1 := by omega
          rw [e, List.getD_cons_succ]
          exact q4
        · intro s' hs'
          rcases List.mem_cons.1 hs' with rfl | hs'
          · exact hcl
          · exact r6 s' hs'
      · split at hr
        · split at hr
          · rename_i y nw0 p0 np0 g0 ng0
            split at hr
            · rename_i hc
              obtain ⟨hy, hp0, hg0⟩ := hc
              obtain ⟨hn, l1, l2⟩ := drop_eq_cons e1.symm
              obtain ⟨pn, p1, p2⟩ := getD_of_drop_eq_cons e2.symm
              obtain ⟨gn, g1, g2⟩ := getD_of_drop_eq_cons e3.symm
              obtain ⟨r1, r2, r3, r4, r0, r5, r6⟩ :=
                replayStep_spec hpos x h ss (j + 1) nw0 np0 ng0 (sz + 1) nw' np' ng' sz' hr
                  l2.symm p2.symm g2.symm
              refine ⟨r1, r2, r3, by omega, fun _ => ?_, ?_, ?_⟩
              · rcases Nat.eq_or_lt_of_le r4 with e | e
                · rw [← e]
                  exact ⟨hn, pn, gn⟩
                · exact r0 e
              · intro p h1 h2
                rcases Nat.eq_or_lt_of_le h1 with rfl | h1
                · refine ⟨hn, by rw [p1, hp0], by rw [g1, hg0]; omega,
                    by rw [g1, hg0]; simp only [List.length_cons]; omega, ?_⟩
                  rw [g1, hg0, Nat.sub_self, List.getD_cons_zero, l1, hy]
                · obtain ⟨hp, q1, q2, q3, q4⟩ := r5 p h1 h2
                  refine ⟨hp, q1, by omega, by simp only [List.length_cons]; omega, ?_⟩
                  have e : gen.getD p 0 - j = (gen.getD p 0 - (j + 1)) + 1 := by omega
                  rw [e, List.getD_cons_succ]
                  exact q4
              · intro s' hs'
                rcases List.mem_cons.1 hs' with rfl | hs'
                · exact hcl
                · exact r6 s' hs'
            · cases hr
          · cases hr
        · cases hr

theorem replayGo_spec [Inhabited α] (hpos : posOK key L pos = true) (steps : List (α → α)) :
    ∀ (f : Nat) (hs : List α) (h : Nat) (nw : List α) (np ng : List Nat) (sz : Nat),
      replayGo key steps pos f hs h nw np ng sz = true →
      hs = L.drop h → nw = L.drop sz → np = par.drop sz → ng = gen.drop sz → h ≤ sz →
      sz ≤ L.length → sz ≤ par.length → sz ≤ gen.length →
      par.length = L.length ∧ gen.length = L.length ∧
        (∀ p, sz ≤ p → ∀ hp : p < L.length, par.getD p 0 < p ∧
          gen.getD p 0 < steps.length ∧
          (steps.getD (gen.getD p 0) id) (L.getD (par.getD p 0) default) = L[p]) ∧
        (L.length ≤ f + h → ∀ q, h ≤ q → ∀ hq : q < L.length, ∀ s ∈ steps,
          ∃ i, ∃ _ : i < L.length, key L[i] = key (s L[q]))
  | 0, hs, h, nw, np, ng, sz, hr, e0, e1, e2, e3, hh, l1, l2, l3 => by
    simp only [replayGo, Bool.and_eq_true, List.isEmpty_iff] at hr
    obtain ⟨⟨n1, n2⟩, n3⟩ := hr
    have m1 := List.drop_eq_nil_iff.1 (e1 ▸ n1)
    have m2 := List.drop_eq_nil_iff.1 (e2 ▸ n2)
    have m3 := List.drop_eq_nil_iff.1 (e3 ▸ n3)
    refine ⟨by omega, by omega, fun p h1 hp => absurd hp (by omega), fun hf q h1 hq => ?_⟩
    omega
  | f + 1, hs, h, nw, np, ng, sz, hr, e0, e1, e2, e3, hh, l1, l2, l3 => by
    simp only [replayGo] at hr
    split at hr
    · rename_i hlt
      split at hr
      · cases hr
      · rename_i x hs'
        split at hr
        · cases hr
        · rename_i nw' np' ng' sz' hst
          obtain ⟨hn, x1, x2⟩ := drop_eq_cons e0.symm
          obtain ⟨r1, r2, r3, r4, r0, r5, r6⟩ :=
            replayStep_spec hpos x h steps 0 nw np ng sz nw' np' ng' sz' hst e1 e2 e3
          have k : sz' ≤ L.length ∧ sz' ≤ par.length ∧ sz' ≤ gen.length := by
            rcases Nat.eq_or_lt_of_le r4 with e | e
            · rw [← e]
              exact ⟨l1, l2, l3⟩
            · exact r0 e
          obtain ⟨i1, i2, i3, i4⟩ := replayGo_spec hpos steps f hs' (h + 1) nw' np' ng' sz' hr
            x2.symm r1 r2 r3 (by omega) k.1 k.2.1 k.2.2
          refine ⟨i1, i2, ?_, ?_⟩
          · intro p h1 hp
            by_cases hp' : p < sz'
            · obtain ⟨_, q1, q2, q3, q4⟩ := r5 p h1 hp'
              have ex : L.getD h default = x := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, x1]
                rfl
              refine ⟨by omega, by simpa using q3, ?_⟩
              rw [q1, ex]
              simpa using q4
            · exact i3 p (by omega) hp
          · intro hf q h1 hq s hs
            rcases Nat.eq_or_lt_of_le h1 with rfl | h1
            · have := r6 s hs
              rwa [x1]
            · exact i4 (by omega) q h1 hq s hs
    · rename_i hge
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hr
      obtain ⟨⟨n1, n2⟩, n3⟩ := hr
      have m1 := List.drop_eq_nil_iff.1 (e1 ▸ n1)
      have m2 := List.drop_eq_nil_iff.1 (e2 ▸ n2)
      have m3 := List.drop_eq_nil_iff.1 (e3 ▸ n3)
      refine ⟨by omega, by omega, fun p h1 hp => absurd hp (by omega), fun hf q h1 hq => ?_⟩
      omega

theorem replay_facts [Inhabited α] {steps : List (α → α)} {base : α} {fuel : Nat}
    (hr : replayOK key steps base fuel L par gen pos = true) :
    posOK key L pos = true ∧ L.head? = some base ∧ par.length = L.length ∧
      gen.length = L.length ∧
      (∀ p, 0 < p → ∀ hp : p < L.length, par.getD p 0 < p ∧ gen.getD p 0 < steps.length ∧
        (steps.getD (gen.getD p 0) id) (L.getD (par.getD p 0) default) = L[p]) ∧
      (L.length ≤ fuel → ∀ x ∈ L, ∀ s ∈ steps, ∃ i, ∃ _ : i < L.length, key L[i] = key (s x)) := by
  unfold replayOK at hr
  rw [Bool.and_eq_true] at hr
  obtain ⟨hpos, hr⟩ := hr
  split at hr
  · rename_i x nw p np g ng
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hgo⟩ := hr
    obtain ⟨i1, i2, i3, i4⟩ := replayGo_spec (L := x :: nw) (par := 0 :: np) (gen := 0 :: ng)
      hpos steps fuel (x :: nw) 0 nw np ng 1 hgo rfl rfl rfl rfl (by omega) (by simp)
      (by simp) (by simp)
    refine ⟨hpos, rfl, i1, i2, fun p h1 hp => i3 p h1 hp, fun hf y hy s hs => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hy
    exact i4 (by omega) q (Nat.zero_le _) hq s hs
  · cases hr

theorem replay_induction [Inhabited α] {steps : List (α → α)} {base : α} {fuel : Nat}
    (hr : replayOK key steps base fuel L par gen pos = true) (P : α → Prop) (h0 : P base)
    (hs : ∀ x, P x → ∀ s ∈ steps, P (s x)) : ∀ y ∈ L, P y := by
  obtain ⟨-, hb, -, -, ht, -⟩ := replay_facts hr
  have key' : ∀ n, ∀ p < n, ∀ hp : p < L.length, P L[p] := by
    intro n
    induction n with
    | zero => intro p hp; omega
    | succ n ih =>
      intro p hpn hp
      rcases Nat.eq_zero_or_pos p with rfl | h1
      · cases L with
        | nil => simp at hp
        | cons x L =>
          have e : x = base := by simpa using hb
          subst e
          exact h0
      · obtain ⟨q1, q2, q3⟩ := ht p h1 hp
        rw [← q3]
        have hpl : par.getD p 0 < L.length := by omega
        have e : L.getD (par.getD p 0) default = L[par.getD p 0] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl]
          rfl
        rw [e]
        refine hs _ (ih _ (by omega) hpl) _ ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem q2]
        exact List.getElem_mem q2
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hy
  exact key' (p + 1) p (Nat.lt_succ_self _) hp

end CFSG.KC.M24G
