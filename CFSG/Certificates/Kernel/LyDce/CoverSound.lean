module

public import Certificates.Data.Kernel.LyDce.Cover

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop CFSG.KC.LyBase CFSG.KC.LyReplay CFSG.KC.MonsterConv.Perm

theorem cvS_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem cvS_strictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem cvS_strictBN (y : Nat) (k : Nat → Bool) : strictBN y k = k y := by
  cases y <;> rfl

theorem cvS_testBit_ones {m l : Nat} : (ones m).testBit l = decide (l < m) := by
  have e : ones m = 2 ^ m - 1 := by
    change 1 <<< m - 1 = _
    rw [Nat.one_shiftLeft]
  rw [e, Nat.testBit_two_pow_sub_one]

theorem cvS_full {R m : Nat} (h : Nat.beq (Nat.land R (ones m)) (ones m) = true) :
    ∀ l < m, R.testBit l = true := by
  intro l hl
  have e := congrArg (fun x => Nat.testBit x l) (Nat.eq_of_beq_eq_true h)
  change (R &&& ones m).testBit l = (ones m).testBit l at e
  rw [Nat.testBit_and, cvS_testBit_ones, decide_eq_true hl, Bool.and_true] at e
  exact e

theorem cvS_rec (g : Nat → Bool) : ∀ k,
    Nat.rec (motive := fun _ => Bool) true (fun l ih => Bool.rec false ih (g l)) k = true →
      ∀ l < k, g l = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | k + 1, h, l, hl => by
    change Bool.rec false (Nat.rec (motive := fun _ => Bool) true
      (fun l ih => Bool.rec false ih (g l)) k) (g k) = true at h
    cases hg : g k
    · rw [hg] at h
      exact absurd h Bool.false_ne_true
    · rw [hg] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact cvS_rec g k h l hl
      · exact hg

theorem cvS_allBelow {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := cvS_rec (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2 ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l))) 64) hi h (i / 64) (by omega)
  have h2 := cvS_rec (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : ((i / 64).shiftLeft 6).add (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : i.blt m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem cvS_testBit_lor_shl {R p q : Nat} (h : (Nat.lor R (Nat.shiftLeft 1 q)).testBit p = true) :
    R.testBit p = true ∨ p = q := by
  change (R ||| 1 <<< q).testBit p = true at h
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_iff] at h
  exact h.imp id Eq.symm

theorem cvS_inner (l : Nat) : ∀ (es : List (Nat × Nat × Nat)) (R : Nat),
    (List.rec (motive := fun _ => Nat → Nat) (fun R => R)
      (fun e _ ih' R => strictN (Nat.lor R (Nat.shiftLeft 1 e.1)) ih') es R).testBit l = true →
    R.testBit l = true ∨ ∃ e ∈ es, e.1 = l
  | [], _, h => Or.inl h
  | e :: es, R, h => by
    dsimp only at h
    rw [cvS_strictN] at h
    rcases cvS_inner l es _ h with h | ⟨e', he', rfl⟩
    · rcases cvS_testBit_lor_shl h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩

theorem cvS_labMask (l : Nat) : ∀ (ws : List (List (Nat × Nat × Nat))) (R : Nat),
    (labMask ws R).testBit l = true → R.testBit l = true ∨ ∃ es ∈ ws, ∃ e ∈ es, e.1 = l
  | [], _, h => Or.inl h
  | es :: ws, R, h => by
    rcases cvS_labMask l ws _ h with h | ⟨es', hes', e, he, rfl⟩
    · rcases cvS_inner l es R h with h | ⟨e, he, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨es, List.mem_cons_self, e, he, rfl⟩
    · exact Or.inr ⟨es', List.mem_cons_of_mem _ hes', e, he, rfl⟩

theorem covOK_sound {ws : List (List (Nat × Nat × Nat))} (h : covOK ws = true) :
    ∀ l < nL, ∃ es ∈ ws, ∃ e ∈ es, e.1 = l := by
  intro l hl
  rcases cvS_labMask l ws 0 (cvS_full h l hl) with h0 | h0
  · rw [Nat.zero_testBit] at h0
    exact absurd h0 Bool.false_ne_true
  · exact h0

theorem incOK_sound {K : Nat} (h : incOK K = true) :
    ∀ l l', l < l' → l' < nL → fldW 48 K l < fldW 48 K l' := by
  have hs := cvS_allBelow h (by decide)
  have hn : nL = 15400 := rfl
  intro l l' hll' hl'
  induction l', hll' using Nat.le_induction with
  | base =>
    have := hs l (by change l < 15400 - 1; rw [hn] at hl'; omega)
    rwa [Nat.blt_eq] at this
  | succ k hk ih =>
    have := hs k (by change k < 15400 - 1; rw [hn] at hl'; omega)
    rw [Nat.blt_eq] at this
    exact Nat.lt_trans (ih (by omega)) this

theorem tabOK_sound {Tc Td Ta Tb Te : Nat} (h : tabOK Tc Td Ta Tb Te = true) :
    ∀ l < nL, fldW 16 Ta l = mvC Tc Td (jC 3) l ∧ fldW 16 Tb l = mvC Tc Td (jC 4) l ∧
      fldW 16 Te l = mvC Tc Td (jC 5) l := by
  intro l hl
  obtain ⟨h1, h2⟩ := cvS_andB (cvS_allBelow h (by decide) l hl)
  obtain ⟨h2, h3⟩ := cvS_andB h2
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem cvS_frOK {T : Tabs} {nt : List (Nat × Nat)} {rep G : List (List Nat)}
    {node root : Nat} {Q : Nat → Prop}
    (hrep : ∀ p, (nt.getD p (0, 0)).1 = node → Q (mvJ T (jwOf (rep.getD p [])) root))
    (hgen : ∀ s l, Q l → Q (mvJ T (jwOf (G.getD s [])) l)) :
    ∀ (es : List (Nat × Nat × Nat)) (R : Nat), (∀ p, R.testBit p = true → Q p) →
      frOK T nt rep G node root es R = true → ∀ l < nL, Q l
  | [], R, hR, h => fun l hl => hR l (cvS_full h l hl)
  | e :: es, R, hR, h => by
    have h' : andB (frEntOK T nt rep G node root R e)
        (strictBN (Nat.lor R (Nat.shiftLeft 1 e.1))
          (fun R => frOK T nt rep G node root es R)) = true := h
    obtain ⟨h1, h2⟩ := cvS_andB h'
    rw [cvS_strictBN] at h2
    have hQ : Q e.1 := by
      unfold frEntOK at h1
      cases hs : Nat.beq e.2.2 0
      · rw [hs] at h1
        obtain ⟨h3, h4⟩ := cvS_andB h1
        have hb : R.testBit e.2.1 = true := by
          have e3 := Nat.eq_of_beq_eq_true h3
          change R >>> e.2.1 &&& 1 = 1 at e3
          have e4 : (R >>> e.2.1).testBit 0 = true := by
            rw [Nat.testBit_zero, ← Nat.and_one_is_mod, e3]
            rfl
          rwa [Nat.testBit_shiftRight, Nat.add_zero] at e4
        rw [Nat.eq_of_beq_eq_true h4]
        exact hgen _ _ (hR _ hb)
      · rw [hs] at h1
        obtain ⟨h3, h4⟩ := cvS_andB h1
        rw [Nat.eq_of_beq_eq_true h4]
        exact hrep _ (Nat.eq_of_beq_eq_true h3)
    refine cvS_frOK hrep hgen es _ ?_ h2
    intro p hp
    rcases cvS_testBit_lor_shl hp with hp | rfl
    · exact hR p hp
    · exact hQ

theorem frOK_sound {T : Tabs} {nt : List (Nat × Nat)} {rep G : List (List Nat)}
    {node root : Nat} {es : List (Nat × Nat × Nat)} {Q : Nat → Prop}
    (hrep : ∀ p, (nt.getD p (0, 0)).1 = node → Q (mvJ T (jwOf (rep.getD p [])) root))
    (hgen : ∀ s l, Q l → Q (mvJ T (jwOf (G.getD s [])) l))
    (h : frOK T nt rep G node root es 0 = true) : ∀ l < nL, Q l := by
  refine cvS_frOK hrep hgen es 0 ?_ h
  intro p hp
  rw [Nat.zero_testBit] at hp
  exact absurd hp Bool.false_ne_true

end CFSG.KC.LyDce

end
