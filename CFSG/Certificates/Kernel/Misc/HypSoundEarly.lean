module

public import Certificates.Data.Kernel.Misc.HypRunE
import CFSG.Certificates.Kernel.Misc.HypSoundSearch

public section

set_option maxRecDepth 100000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

def SubB (a b : Nat) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

private theorem subB_refl (a : Nat) : SubB a a := fun _ h => h

private theorem subB_trans {a b c : Nat} (h1 : SubB a b) (h2 : SubB b c) : SubB a c :=
  fun i h => h2 i (h1 i h)

private theorem subB_or_left (a b : Nat) : SubB a (Nat.lor a b) := by
  intro i h
  change (a ||| b).testBit i = true
  rw [Nat.testBit_or, h, Bool.true_or]

private theorem subB_or_right (a b : Nat) : SubB a (Nat.lor b a) := by
  intro i h
  change (b ||| a).testBit i = true
  rw [Nat.testBit_or, h, Bool.or_true]

private theorem testBit_conf (a m i : Nat) :
    (Nat.land (Nat.land a (Nat.shiftRight a 693)) m).testBit i =
      (a.testBit i && a.testBit (693 + i) && m.testBit i) := by
  change ((a &&& (a >>> 693)) &&& m).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight]

private theorem conf_mono {a b m : Nat} (h : SubB a b)
    (ha : Nat.land (Nat.land a (Nat.shiftRight a 693)) m ≠ 0) :
    Nat.land (Nat.land b (Nat.shiftRight b 693)) m ≠ 0 := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero ha
  intro hb
  have hb' : (Nat.land (Nat.land b (Nat.shiftRight b 693)) m).testBit i = false := by
    rw [hb, Nat.zero_testBit]
  rw [testBit_conf] at hi hb'
  simp only [Bool.and_eq_true] at hi
  rw [h _ hi.1.1, h _ hi.1.2, hi.2] at hb'
  exact absurd hb' (by decide)

private theorem stopK_iff (a : Nat) : stopK a = true ↔ a.testBit 1386 = true ∨
    (a.testBit 1387 = true ∧
      Nat.land (Nat.land a (Nat.shiftRight a 693)) (Nat.sub (Nat.shiftLeft 1 693) 1) ≠ 0) := by
  unfold stopK
  rw [bitK_eq_testBit, bitK_eq_testBit, orB_eq, andB_eq, notB_eq]
  cases hz : Nat.beq (Nat.land (Nat.land a (Nat.shiftRight a 693))
    (Nat.sub (Nat.shiftLeft 1 693) 1)) 0
  · have hz' := Nat.ne_of_beq_eq_false hz
    rw [Bool.not_false, Bool.and_true, Bool.or_eq_true]
    exact ⟨fun h => h.imp_right fun h => ⟨h, hz'⟩, fun h => h.imp_right And.left⟩
  · have hz' := Nat.eq_of_beq_eq_true hz
    rw [Bool.not_true, Bool.and_false, Bool.or_false]
    exact ⟨Or.inl, fun h => h.elim id fun h => absurd hz' h.2⟩

private theorem stopK_mono {a b : Nat} (h : SubB a b) (hs : stopK a = true) : stopK b = true := by
  rw [stopK_iff] at hs ⊢
  rcases hs with hs | ⟨h1, h2⟩
  · exact Or.inl (h _ hs)
  · exact Or.inr ⟨h _ h1, conf_mono h h2⟩

private theorem rec_stop {f g : Nat → Nat → Nat} {s : Nat → Bool} (init : Nat)
    (hg : ∀ x a, SubB a (g x a)) (hf1 : ∀ x a, s a = false → f x a = g x a)
    (hf2 : ∀ x a, s a = true → f x a = a) (hs : ∀ a b, SubB a b → s a = true → s b = true)
    (n : Nat) :
    Nat.rec (motive := fun _ => Nat) init f n = Nat.rec (motive := fun _ => Nat) init g n ∨
      (s (Nat.rec (motive := fun _ => Nat) init f n) = true ∧
        SubB (Nat.rec (motive := fun _ => Nat) init f n) (Nat.rec (motive := fun _ => Nat) init g n)) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    change f n (Nat.rec (motive := fun _ => Nat) init f n) =
        g n (Nat.rec (motive := fun _ => Nat) init g n) ∨
      (s (f n (Nat.rec (motive := fun _ => Nat) init f n)) = true ∧
        SubB (f n (Nat.rec (motive := fun _ => Nat) init f n))
          (g n (Nat.rec (motive := fun _ => Nat) init g n)))
    rcases ih with h | ⟨h1, h2⟩
    · rw [h]
      cases hsa : s (Nat.rec (motive := fun _ => Nat) init g n)
      · exact Or.inl (hf1 _ _ hsa)
      · rw [hf2 _ _ hsa]
        exact Or.inr ⟨hsa, hg _ _⟩
    · rw [hf2 _ _ h1]
      exact Or.inr ⟨h1, subB_trans h2 (hg _ _)⟩

private theorem subB_rec {a y : Nat} (c : Bool) (h : SubB a y) :
    SubB a (Bool.rec (motive := fun _ => Nat) a y c) := by
  cases c
  · exact subB_refl a
  · exact h

private theorem subB_body (LB : Nat → Nat) (NL : Nat → List Nat) (x j a : Nat) (c1 c2 : Bool) :
    SubB a (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) a
        (Nat.lor (Nat.shiftLeft 1 1387) (extK LB NL x j a)) c2)
      (Nat.lor a (Nat.shiftLeft 1 1386)) c1) := by
  cases c1
  · cases c2
    · exact subB_refl a
    · rw [hypCand_extK_or]
      exact subB_trans (subB_or_left a _) (subB_or_right _ _)
  · exact subB_or_left a _

private theorem andB_notB_false (c : Bool) : andB c (notB false) = c := by cases c <;> rfl

private theorem andB_notB_true (c : Bool) : andB c (notB true) = false := by cases c <;> rfl

@[expose] noncomputable def stepK (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X x acc : Nat) :
    Nat :=
  letN acc fun acc => Bool.rec (motive := fun _ => Nat) acc
    (letN (candK LI NL x I X) fun C =>
      Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) acc
          (Nat.lor (Nat.shiftLeft 1 1387) (extK LB NL x (bitPosK C) acc))
          (Nat.beq (Nat.land C (Nat.sub C 1)) 0))
        (Nat.lor acc (Nat.shiftLeft 1 1386)) (Nat.beq C 0))
    (andB (bitK I x) (notB (Nat.beq (Nat.land (PB x)
      (Nat.xor (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1))) 0)))

@[expose] noncomputable def stepE (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X x acc : Nat) :
    Nat :=
  letN acc fun acc => Bool.rec (motive := fun _ => Nat) acc
    (letN (candK LI NL x I X) fun C =>
      Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) acc
          (Nat.lor (Nat.shiftLeft 1 1387) (extK LB NL x (bitPosK C) acc))
          (Nat.beq (Nat.land C (Nat.sub C 1)) 0))
        (Nat.lor acc (Nat.shiftLeft 1 1386)) (Nat.beq C 0))
    (andB (andB (bitK I x) (notB (Nat.beq (Nat.land (PB x)
      (Nat.xor (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1))) 0))) (notB (stopK acc)))

private theorem passK_eq (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat) :
    passK PB LB LI NL I X =
      Nat.rec (motive := fun _ => Nat) (Nat.lor I (Nat.shiftLeft X 693)) (stepK PB LB LI NL I X)
        693 := by
  unfold passK
  rw [letN_eq]
  rfl

private theorem passE_eq (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat) :
    passE PB LB LI NL I X =
      Nat.rec (motive := fun _ => Nat) (Nat.lor I (Nat.shiftLeft X 693)) (stepE PB LB LI NL I X)
        693 := by
  unfold passE
  rw [letN_eq]
  rfl

theorem passE_cases (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat) :
    passE PB LB LI NL I X = passK PB LB LI NL I X ∨
      (stopK (passE PB LB LI NL I X) = true ∧
        SubB (passE PB LB LI NL I X) (passK PB LB LI NL I X)) := by
  rw [passE_eq, passK_eq]
  refine rec_stop (f := stepE PB LB LI NL I X) (g := stepK PB LB LI NL I X) (s := stopK) _ ?_ ?_ ?_
    (fun a b h hs => stopK_mono h hs) 693
  · intro x a
    unfold stepK
    simp only [letN_eq]
    exact subB_rec _ (subB_body _ _ _ _ _ _ _)
  · intro x a hs
    unfold stepE stepK
    simp only [letN_eq]
    rw [hs, andB_notB_false]
  · intro x a hs
    unfold stepE
    simp only [letN_eq]
    rw [hs, andB_notB_true]

@[expose] noncomputable def tailG (PB LB LI : Nat → Nat) (NL : Nat → List Nat)
    (go : Nat → Nat → Nat) (I X r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (letN (minAccK PB LI NL I X) fun a => Bool.rec (motive := fun _ => Nat)
        (letN (Nat.mod a 1024) fun x =>
          branchK LB NL go x (candK LI NL x I X) (Nat.lor I (Nat.shiftLeft X 693)))
        0 (Nat.beq a (Nat.mul 1024 2048)))
      (go (Nat.land r (Nat.sub (Nat.shiftLeft 1 693) 1))
        (Nat.land (Nat.shiftRight r 693) (Nat.sub (Nat.shiftLeft 1 693) 1)))
      (bitK r 1387))
    1 (bitK r 1386)

@[expose] noncomputable def runG (PB LB LI : Nat → Nat) (NL : Nat → List Nat)
    (pass : Nat → Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0) (fun _ ih I X => letN I fun I =>
    letN X fun X => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (letN (pass I X) fun r => tailG PB LB LI NL ih I X r)
        (Nat.add 2 I) (Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)))
      1 (notB (Nat.beq (Nat.land I X) 0))) fuel

private theorem runK_eq_runG (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (n : Nat) :
    runK PB LB LI NL n = runG PB LB LI NL (passK PB LB LI NL) n := rfl

private theorem runKE_eq_runG (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (n : Nat) :
    runKE PB LB LI NL n = runG PB LB LI NL (passE PB LB LI NL) n := rfl

private theorem runG_succ (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (p : Nat → Nat → Nat)
    (n I X : Nat) : runG PB LB LI NL p (n + 1) I X =
      Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (tailG PB LB LI NL (runG PB LB LI NL p n) I X (p I X))
          (Nat.add 2 I) (Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)))
        1 (notB (Nat.beq (Nat.land I X) 0)) := by
  change letN I (fun I => letN X fun X => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (letN (p I X) fun r => tailG PB LB LI NL (runG PB LB LI NL p n) I X r)
        (Nat.add 2 I) (Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)))
      1 (notB (Nat.beq (Nat.land I X) 0))) = _
  simp only [letN_eq]

private theorem runG_conf (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (p : Nat → Nat → Nat)
    (n a b : Nat) (h : Nat.land a b ≠ 0) :
    runG PB LB LI NL p n a b = Nat.rec (motive := fun _ => Nat) 0 (fun _ _ => 1) n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [runG_succ]
    have hb : notB (Nat.beq (Nat.land a b) 0) = true := by
      cases hz : Nat.beq (Nat.land a b) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hz) h
    rw [hb]

private theorem next_conf {r : Nat}
    (h : Nat.land (Nat.land r (Nat.shiftRight r 693)) (Nat.sub (Nat.shiftLeft 1 693) 1) ≠ 0) :
    Nat.land (Nat.land r (Nat.sub (Nat.shiftLeft 1 693) 1))
      (Nat.land (Nat.shiftRight r 693) (Nat.sub (Nat.shiftLeft 1 693) 1)) ≠ 0 := by
  intro h0
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (fun z => z.testBit i) h0
  simp only [Nat.zero_testBit] at e ⊢
  rw [testBit_conf]
  change ((r &&& Nat.sub (Nat.shiftLeft 1 693) 1) &&&
    ((r >>> 693) &&& Nat.sub (Nat.shiftLeft 1 693) 1)).testBit i = false at e
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight] at e
  cases h1 : r.testBit i <;> cases h2 : r.testBit (693 + i) <;>
    cases h3 : (Nat.sub (Nat.shiftLeft 1 693) 1).testBit i <;> simp_all

private theorem combK_ne {a b : Nat} (h : combK a b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro ha
    subst ha
    apply h
    unfold combK
    rw [letN_eq, letN_eq]
    rfl
  · intro hb
    subst hb
    apply h
    unfold combK
    rw [letN_eq, letN_eq]
    cases Nat.beq a 0 <;> rfl

private theorem branch_rec_congr (LB : Nat → Nat) (NL : Nat → List Nat) (go go' : Nat → Nat → Nat)
    (x C S : Nat) (hgo : ∀ a b, go' a b ≠ 0 → go' a b = go a b) (k : Nat) :
    Nat.rec (motive := fun _ => Nat) 1 (fun j acc => letN acc fun acc =>
      Bool.rec (motive := fun _ => Nat) acc
        (letN (extK LB NL x j S) fun S' =>
          combK acc (go' (Nat.land S' (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftRight S' 693)))
        (bitK C j)) k ≠ 0 →
    Nat.rec (motive := fun _ => Nat) 1 (fun j acc => letN acc fun acc =>
      Bool.rec (motive := fun _ => Nat) acc
        (letN (extK LB NL x j S) fun S' =>
          combK acc (go' (Nat.land S' (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftRight S' 693)))
        (bitK C j)) k =
    Nat.rec (motive := fun _ => Nat) 1 (fun j acc => letN acc fun acc =>
      Bool.rec (motive := fun _ => Nat) acc
        (letN (extK LB NL x j S) fun S' =>
          combK acc (go (Nat.land S' (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftRight S' 693)))
        (bitK C j)) k := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [letN_eq] at h ih ⊢
    cases hc : bitK C k
    · rw [hc] at h
      exact ih h
    · rw [hc] at h
      obtain ⟨h1, h2⟩ := combK_ne h
      rw [ih h1, hgo _ _ h2]

private theorem branchK_congr (LB : Nat → Nat) (NL : Nat → List Nat) (go go' : Nat → Nat → Nat)
    (x C S : Nat) (hgo : ∀ a b, go' a b ≠ 0 → go' a b = go a b)
    (h : branchK LB NL go' x C S ≠ 0) : branchK LB NL go' x C S = branchK LB NL go x C S :=
  branch_rec_congr LB NL go go' x C S hgo 1024 h

private theorem tailG_congr (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (go go' : Nat → Nat → Nat)
    (I X r : Nat) (hgo : ∀ a b, go' a b ≠ 0 → go' a b = go a b)
    (h : tailG PB LB LI NL go' I X r ≠ 0) :
    tailG PB LB LI NL go' I X r = tailG PB LB LI NL go I X r := by
  unfold tailG at h ⊢
  simp only [letN_eq] at h ⊢
  cases h1 : bitK r 1386
  · rw [h1] at h
    cases h2 : bitK r 1387
    · rw [h2] at h
      cases h3 : Nat.beq (minAccK PB LI NL I X) (Nat.mul 1024 2048)
      · rw [h3] at h
        exact branchK_congr LB NL go go' _ _ _ hgo h
      · rfl
    · rw [h2] at h
      exact hgo _ _ h
  · rfl

private theorem runG_eq (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (p1 p2 : Nat → Nat → Nat)
    (hp : ∀ I X, p1 I X = p2 I X ∨ (stopK (p1 I X) = true ∧ SubB (p1 I X) (p2 I X))) (n : Nat) :
    ∀ I X, runG PB LB LI NL p1 n I X ≠ 0 →
      runG PB LB LI NL p1 n I X = runG PB LB LI NL p2 n I X := by
  induction n with
  | zero => intro I X h; exact absurd rfl h
  | succ n ih =>
    intro I X h
    rw [runG_succ] at h ⊢
    rw [runG_succ]
    cases hc1 : notB (Nat.beq (Nat.land I X) 0)
    · rw [hc1] at h
      cases hc2 : Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)
      · rw [hc2] at h
        change tailG PB LB LI NL (runG PB LB LI NL p1 n) I X (p1 I X) ≠ 0 at h
        change tailG PB LB LI NL (runG PB LB LI NL p1 n) I X (p1 I X) =
          tailG PB LB LI NL (runG PB LB LI NL p2 n) I X (p2 I X)
        rcases hp I X with he | ⟨hs, hsub⟩
        · rw [he] at h ⊢
          exact tailG_congr PB LB LI NL _ _ I X _ ih h
        · rw [stopK_iff] at hs
          unfold tailG at h ⊢
          simp only [bitK_eq_testBit] at h ⊢
          rcases hs with h86 | ⟨h87, hcf⟩
          · rw [h86, hsub _ h86]
          · cases h86 : (p1 I X).testBit 1386
            · rw [h86, h87] at h
              change runG PB LB LI NL p1 n _ _ ≠ 0 at h
              rw [h87]
              change runG PB LB LI NL p1 n _ _ = _
              rw [runG_conf PB LB LI NL p1 n _ _ (next_conf hcf)] at h ⊢
              cases h86' : (p2 I X).testBit 1386
              · rw [hsub _ h87]
                change _ = runG PB LB LI NL p2 n _ _
                rw [runG_conf PB LB LI NL p2 n _ _ (next_conf (conf_mono hsub hcf))]
              · cases n with
                | zero => exact absurd rfl h
                | succ n => rfl
            · rw [hsub _ h86]
      · rfl
    · rfl

theorem runKE_eq (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (n I X : Nat)
    (h : runKE PB LB LI NL n I X ≠ 0) : runKE PB LB LI NL n I X = runK PB LB LI NL n I X := by
  rw [runKE_eq_runG] at h ⊢
  rw [runK_eq_runG]
  exact runG_eq PB LB LI NL _ _ (passE_cases PB LB LI NL) n I X h

private theorem chk_ne {e r : Nat} {HS : Nat → Nat}
    (h : Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt e 4225) (Nat.beq r (Nat.add 2 (HS (Nat.pred e))))) (Nat.beq r 1)
      (Nat.beq e 0) = true) : r ≠ 0 := by
  intro hr
  subst hr
  cases hb : Nat.beq e 0
  · rw [hb, andB_eq, Bool.and_eq_true] at h
    have h2 := Nat.eq_of_beq_eq_true h.2
    rw [Nat.add_eq] at h2
    omega
  · rw [hb] at h
    exact Bool.false_ne_true h

theorem searchK_of_searchKE {PB LB HS LI : Nat → Nat} {NL : Nat → List Nat} {RES lo n : Nat}
    (h : searchKE PB LB HS LI NL RES lo n = true) : searchK PB LB HS LI NL RES lo n = true := by
  unfold searchKE at h
  unfold searchK
  rw [letB_eq, allN_lqt_iff] at h ⊢
  intro d hd
  have h1 := h d hd
  rw [letB_eq] at h1 ⊢
  rw [impB_eq] at h1 ⊢
  cases hb : Nat.blt (Nat.add lo d) 1024
  · rfl
  · rw [hb] at h1
    simp only [Bool.not_true, Bool.false_or, letB_eq] at h1 ⊢
    rw [← runKE_eq PB LB LI NL _ _ _ (chk_ne h1)]
    exact h1

end CFSG.KC.Misc.Hyp

end
