module

public import CFSG.Certificates.Kernel.Th.Spec.Big

public section

namespace CFSG.KC.Th.Spec.FwdSlp

open CFSG.KC.Th CFSG.KC.Th.BigS

variable {RB : ℕ → ℕ} {c rm ONE : ℕ}

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem regBelow_spec {a r : ℕ} (h : regBelow a r = true) : 0 < a ∧ a < r := by
  obtain ⟨h1, h2⟩ := andB_eq_true h
  exact ⟨by simpa using h1, by simpa using h2⟩

private noncomputable def innerLoop (f : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih J S => CFSG.KC.Loop.strictN (f S (bitsN J 0 28)) (ih (J >>> 28)))

private noncomputable def chunkLoop (f : ℕ → ℕ → ℕ) (Cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => CFSG.KC.Loop.strictN (innerLoop f (C &&& 255) (C >>> 8) S) ih) Cs

private noncomputable def instrs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, J => bitsN J 0 28 :: instrs n (J >>> 28)

private noncomputable def prog : List ℕ → List ℕ
  | [] => []
  | C :: Cs => instrs (C &&& 255) (C >>> 8) ++ prog Cs

private theorem innerLoop_succ (f : ℕ → ℕ → ℕ) (n J S : ℕ) :
    innerLoop f (n + 1) J S = innerLoop f n (J >>> 28) (f S (bitsN J 0 28)) := by
  have e : innerLoop f (n + 1) J S =
      CFSG.KC.Loop.strictN (f S (bitsN J 0 28)) (innerLoop f n (J >>> 28)) := rfl
  rw [e, strictN_eq]

private theorem innerLoop_eq (f : ℕ → ℕ → ℕ) :
    ∀ n J S, innerLoop f n J S = (instrs n J).foldl f S
  | 0, _, _ => rfl
  | n + 1, J, S => by rw [innerLoop_succ, innerLoop_eq f n, instrs, List.foldl_cons]

private theorem chunkLoop_cons (f : ℕ → ℕ → ℕ) (C : ℕ) (Cs : List ℕ) (S : ℕ) :
    chunkLoop f (C :: Cs) S = chunkLoop f Cs (innerLoop f (C &&& 255) (C >>> 8) S) := by
  have e : chunkLoop f (C :: Cs) S =
      CFSG.KC.Loop.strictN (innerLoop f (C &&& 255) (C >>> 8) S) (chunkLoop f Cs) := rfl
  rw [e, strictN_eq]

private theorem chunkLoop_eq (f : ℕ → ℕ → ℕ) :
    ∀ Cs S, chunkLoop f Cs S = (prog Cs).foldl f S
  | [], _ => rfl
  | C :: Cs, S => by
    rw [chunkLoop_cons, chunkLoop_eq f Cs, innerLoop_eq, prog, List.foldl_append]

private noncomputable def slpStep (RB : ℕ → ℕ) (c rm ONE S ins : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (S + 1) (andB (Nat.blt 0 S) (insOK RB c rm ONE S ins))

private theorem runSlp_eq (RB : ℕ → ℕ) (c rm ONE : ℕ) (Cs : List ℕ) (S : ℕ) :
    runSlp RB c rm ONE Cs S = (prog Cs).foldl (slpStep RB c rm ONE) S := by
  have e : runSlp RB c rm ONE Cs S = chunkLoop (slpStep RB c rm ONE) Cs S := rfl
  rw [e, chunkLoop_eq]

private theorem slpStep_zero (ins : ℕ) : slpStep RB c rm ONE 0 ins = 0 := rfl

private theorem foldl_slpStep_zero : ∀ L : List ℕ, L.foldl (slpStep RB c rm ONE) 0 = 0
  | [] => rfl
  | ins :: L => by rw [List.foldl_cons, slpStep_zero]; exact foldl_slpStep_zero L

private theorem slpStep_pos {S ins : ℕ} (h : 0 < slpStep RB c rm ONE S ins) :
    slpStep RB c rm ONE S ins = S + 1 ∧ 0 < S ∧ insOK RB c rm ONE S ins = true := by
  unfold slpStep at h ⊢
  cases hb : andB (Nat.blt 0 S) (insOK RB c rm ONE S ins)
  · rw [hb] at h
    exact absurd h (Nat.lt_irrefl 0)
  · obtain ⟨h1, h2⟩ := andB_eq_true hb
    exact ⟨rfl, by simpa using h1, h2⟩

private noncomputable def insF (RB : ℕ → ℕ) (c rm ONE r k a b e : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (andB (regBelow a r) (Nat.beq (mulB c rm (RB a) (RB r)) ONE)) (Nat.beq k 2))
      (andB (regBelow a r) (andB (Nat.blt 0 e) (Nat.beq (RB r) (powB c rm ONE (RB a) e 4))))
      (Nat.beq k 1))
    (andB (regBelow a r) (andB (regBelow b r) (Nat.beq (RB r) (mulB c rm (RB a) (RB b)))))
    (Nat.beq k 0)

private theorem insOK_eq (r ins : ℕ) : insOK RB c rm ONE r ins =
    insF RB c rm ONE r (ins &&& 3) (bitsN ins 2 11) (bitsN ins 13 11) (bitsN ins 24 4) := rfl

private theorem insF_cases {r k a b e : ℕ} (h : insF RB c rm ONE r k a b e = true) :
    (k = 0 ∧ (0 < a ∧ a < r) ∧ (0 < b ∧ b < r) ∧ RB r = mulB c rm (RB a) (RB b)) ∨
      ((0 < a ∧ a < r) ∧ 0 < e ∧ RB r = powB c rm ONE (RB a) e 4) ∨
      ((0 < a ∧ a < r) ∧ mulB c rm (RB a) (RB r) = ONE) := by
  unfold insF at h
  cases h0 : Nat.beq k 0
  · rw [h0] at h
    cases h1 : Nat.beq k 1
    · rw [h1] at h
      cases h2 : Nat.beq k 2
      · rw [h2] at h
        exact absurd h Bool.false_ne_true
      · rw [h2] at h
        obtain ⟨ha, hm⟩ := andB_eq_true h
        exact Or.inr (Or.inr ⟨regBelow_spec ha, Nat.eq_of_beq_eq_true hm⟩)
    · rw [h1] at h
      obtain ⟨ha, h'⟩ := andB_eq_true h
      obtain ⟨he, hp⟩ := andB_eq_true h'
      exact Or.inr (Or.inl ⟨regBelow_spec ha, by simpa using he, Nat.eq_of_beq_eq_true hp⟩)
  · rw [h0] at h
    obtain ⟨ha, h'⟩ := andB_eq_true h
    obtain ⟨hb, hm⟩ := andB_eq_true h'
    exact Or.inl ⟨Nat.eq_of_beq_eq_true h0, regBelow_spec ha, regBelow_spec hb,
      Nat.eq_of_beq_eq_true hm⟩

private theorem Q_of_insOK (Q : ℕ → Prop)
    (hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r)
    (hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r)
    (hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r) {r ins : ℕ}
    (h : insOK RB c rm ONE r ins = true)
    (hQ : ∀ j, 0 < j → j < r →
      (j = bitsN ins 2 11 ∨ (ins &&& 3 = 0 ∧ j = bitsN ins 13 11)) → Q j) :
    Q r := by
  rw [insOK_eq] at h
  have he : bitsN ins 24 4 < 16 := by
    rw [bitsN_eq]
    exact Nat.mod_lt _ (Nat.two_pow_pos 4)
  rcases insF_cases h with ⟨hk, ha, hb, hr⟩ | ⟨ha, he0, hr⟩ | ⟨ha, hr⟩
  · exact hmul r _ _ (hQ _ ha.1 ha.2 (Or.inl rfl)) (hQ _ hb.1 hb.2 (Or.inr ⟨hk, rfl⟩)) hr
  · exact hpow r _ _ (hQ _ ha.1 ha.2 (Or.inl rfl)) he0 he hr
  · exact hinv r _ (hQ _ ha.1 ha.2 (Or.inl rfl)) hr

private theorem foldl_slp_pos {ins S : ℕ} {L : List ℕ}
    (h : 0 < (ins :: L).foldl (slpStep RB c rm ONE) S) : 0 < slpStep RB c rm ONE S ins := by
  rw [List.foldl_cons] at h
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0, foldl_slpStep_zero] at h
  exact Nat.lt_irrefl 0 h

private theorem foldl_slp_le : ∀ (L : List ℕ) (S : ℕ), 0 < L.foldl (slpStep RB c rm ONE) S →
    S ≤ L.foldl (slpStep RB c rm ONE) S
  | [], _, _ => Nat.le_refl _
  | ins :: L, S, h => by
    obtain ⟨e, -, -⟩ := slpStep_pos (foldl_slp_pos h)
    rw [List.foldl_cons, e] at h ⊢
    have := foldl_slp_le L (S + 1) h
    omega

private theorem foldl_slp_induct (Q : ℕ → Prop)
    (hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r)
    (hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r)
    (hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r) :
    ∀ (L : List ℕ) (S : ℕ), (∀ k, 0 < k → k < S → Q k) →
      0 < L.foldl (slpStep RB c rm ONE) S → ∀ k, 0 < k → k < L.foldl (slpStep RB c rm ONE) S → Q k
  | [], _, hS, _ => hS
  | ins :: L, S, hS, h => by
    obtain ⟨e, -, hins⟩ := slpStep_pos (foldl_slp_pos h)
    rw [List.foldl_cons, e] at h ⊢
    refine foldl_slp_induct Q hmul hpow hinv L (S + 1) (fun k hk hkS => ?_) h
    by_cases hk' : k < S
    · exact hS k hk hk'
    · obtain rfl : k = S := by omega
      exact Q_of_insOK Q hmul hpow hinv hins (fun j hj hjS _ => hS j hj hjS)

private noncomputable def markF (m r k a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) m (m ||| 1 <<< r)
    (Bool.rec (motive := fun _ => Bool) (marked m a) (andB (marked m a) (marked m b))
      (Nat.beq k 0))

private noncomputable def markStep (S ins : ℕ) : ℕ :=
  ((S &&& 2047) + 1) |||
    markF (S >>> 11) (S &&& 2047) (ins &&& 3) (bitsN ins 2 11) (bitsN ins 13 11) <<< 11

private theorem runMarked_eq (Cs : List ℕ) (S : ℕ) :
    runMarked Cs S = (prog Cs).foldl markStep S := by
  have e : runMarked Cs S = chunkLoop markStep Cs S := rfl
  rw [e, chunkLoop_eq]

private theorem marked_eq (m r : ℕ) : marked m r = m.testBit r := by
  have e : marked m r = Nat.blt 0 (m &&& 2 ^ r) := by
    show Nat.blt 0 (m &&& 1 <<< r) = _
    rw [Nat.one_shiftLeft]
  rw [e]
  cases h : m.testBit r
  · have h0 : m &&& 2 ^ r = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : r = i
      · subst hi
        simp [h]
      · simp [hi]
    rw [h0]
    rfl
  · have h1 : (m &&& 2 ^ r).testBit r = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow_self, h]
      rfl
    have h2 : m &&& 2 ^ r ≠ 0 := fun h0 => by
      rw [h0, Nat.zero_testBit] at h1
      exact Bool.false_ne_true h1
    exact Nat.blt_eq.mpr (Nat.pos_of_ne_zero h2)

private theorem marked_markF {m r k a b j : ℕ} (h : marked (markF m r k a b) j = true) :
    marked m j = true ∨ (j = r ∧ marked m a = true ∧ (k = 0 → marked m b = true)) := by
  have key : ∀ cond : Bool,
      marked (Bool.rec (motive := fun _ => ℕ) m (m ||| 1 <<< r) cond) j = true →
        marked m j = true ∨ (j = r ∧ cond = true) := by
    intro cond hc
    cases cond
    · exact Or.inl hc
    · change marked (m ||| 1 <<< r) j = true at hc
      rw [marked_eq, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_iff, ← marked_eq] at hc
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨hc.symm, rfl⟩
  rcases key _ h with h' | ⟨hj, hc⟩
  · exact Or.inl h'
  · refine Or.inr ⟨hj, ?_, fun hk => ?_⟩
    · cases h0 : Nat.beq k 0
      · rw [h0] at hc
        exact hc
      · rw [h0] at hc
        exact (andB_eq_true hc).1
    · have h0 : Nat.beq k 0 = true := by simp [hk]
      rw [h0] at hc
      exact (andB_eq_true hc).2

private theorem markStep_eq {S : ℕ} (m : ℕ) (hS : S + 1 < 2048) (ins : ℕ) :
    markStep (S + 2048 * m) ins =
      S + 1 + 2048 * markF m S (ins &&& 3) (bitsN ins 2 11) (bitsN ins 13 11) := by
  have p11 : (2 : ℕ) ^ 11 = 2048 := rfl
  have h1 : (S + 2048 * m) &&& 2047 = S := by
    rw [show (2047 : ℕ) = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, p11]
    omega
  have h2 : (S + 2048 * m) >>> 11 = m := by
    rw [Nat.shiftRight_eq_div_pow, p11]
    omega
  unfold markStep
  rw [h1, h2, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt (show S + 1 < 2 ^ 11 by rw [p11]; omega),
    Nat.shiftLeft_eq, p11]
  omega

private theorem foldl_marked (Q : ℕ → Prop)
    (hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r)
    (hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r)
    (hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r) :
    ∀ (L : List ℕ) (S m : ℕ), (∀ k, marked m k = true → Q k) →
      0 < L.foldl (slpStep RB c rm ONE) S → L.foldl (slpStep RB c rm ONE) S < 2048 →
      ∃ m', L.foldl markStep (S + 2048 * m) = L.foldl (slpStep RB c rm ONE) S + 2048 * m' ∧
        ∀ k, marked m' k = true → Q k
  | [], _, m, hm, _, _ => ⟨m, rfl, hm⟩
  | ins :: L, S, m, hm, h, hlt => by
    obtain ⟨e, -, hins⟩ := slpStep_pos (foldl_slp_pos h)
    rw [List.foldl_cons, e] at h hlt
    simp only [List.foldl_cons]
    rw [e]
    have hle := foldl_slp_le L (S + 1) h
    rw [markStep_eq m (by omega) ins]
    refine foldl_marked Q hmul hpow hinv L (S + 1) _ (fun k hk => ?_) h hlt
    rcases marked_markF hk with hk' | ⟨rfl, ha, hb⟩
    · exact hm k hk'
    · refine Q_of_insOK Q hmul hpow hinv hins (fun j _ _ hj => ?_)
      rcases hj with rfl | ⟨h3, rfl⟩
      · exact hm _ ha
      · exact hm _ (hb h3)

theorem runSlp_induct (Q : ℕ → Prop)
    (hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r)
    (hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r)
    (hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r)
    (Cs : List ℕ) (S : ℕ) (hS : ∀ k, 0 < k → k < S → Q k)
    (hpos : 0 < runSlp RB c rm ONE Cs S) :
    ∀ k, 0 < k → k < runSlp RB c rm ONE Cs S → Q k := by
  rw [runSlp_eq] at hpos ⊢
  exact foldl_slp_induct Q hmul hpow hinv _ S hS hpos

theorem runMarked_induct (Q : ℕ → Prop)
    (hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r)
    (hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r)
    (hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r)
    (Cs : List ℕ) (S m : ℕ) (hm : ∀ k, marked m k = true → Q k)
    (hpos : 0 < runSlp RB c rm ONE Cs S) (hlt : runSlp RB c rm ONE Cs S < 2048) :
    runMarked Cs (S + 2048 * m) % 2048 = runSlp RB c rm ONE Cs S ∧
      ∀ k, marked (runMarked Cs (S + 2048 * m) / 2048) k = true → Q k := by
  rw [runSlp_eq] at hpos hlt
  rw [runMarked_eq, runSlp_eq]
  obtain ⟨m', e, hm'⟩ := foldl_marked Q hmul hpow hinv _ S m hm hpos hlt
  rw [e]
  refine ⟨by omega, fun k hk => hm' k ?_⟩
  rwa [show ((prog Cs).foldl (slpStep RB c rm ONE) S + 2048 * m') / 2048 = m' by omega] at hk

end CFSG.KC.Th.Spec.FwdSlp

end
