module

public import CFSG.Certificates.Kernel.Misc.HypSearchCtx
public import CFSG.Certificates.Kernel.Misc.XiSound

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

variable {C : HCtx} {PB LB LI GI : Nat → Nat} {PL NL : Nat → List Nat}

private theorem land_ne_zero_iff {I X : Nat} (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    I &&& X ≠ 0 ↔ ∃ p < 693, I.testBit p = true ∧ X.testBit p = true := by
  constructor
  · intro hne
    by_contra h
    apply hne
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hp : p < 693
    · have h1 : ¬ (I.testBit p = true ∧ X.testBit p = true) := fun hc => h ⟨p, hp, hc⟩
      cases hi : I.testBit p <;> cases hx : X.testBit p <;> simp_all
    · have hi : I.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hI
          (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.1 hp)))
      have hx : X.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hX
          (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.1 hp)))
      simp [hi, hx]
  · rintro ⟨p, hp, hi, hx⟩ hzero
    have h1 : (I &&& X).testBit p = true := by rw [Nat.testBit_and, hi, hx]; rfl
    rw [hzero] at h1
    simp at h1

private theorem lor_eq_all_ones_iff {I X : Nat} (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    I ||| X = 2 ^ 693 - 1 ↔ ∀ p < 693, I.testBit p = true ∨ X.testBit p = true := by
  constructor
  · intro h p hp
    have h1 := congrArg (fun n => n.testBit p) h
    rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one, decide_eq_true hp, Bool.or_eq_true] at h1
    exact h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
    by_cases hp : p < 693
    · rw [decide_eq_true hp, Bool.or_eq_true]
      exact h p hp
    · have hi : I.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hI
          (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.1 hp)))
      have hx : X.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hX
          (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.1 hp)))
      rw [decide_eq_false hp, hi, hx]
      rfl

theorem anyIn_conflict_iff {I X : Nat} (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    anyIn 693 (fun p => (fl I)[p]! && (fl X)[p]!) = true ↔ I &&& X ≠ 0 := by
  rw [anyIn_iff]
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨p, hp, hI', hX'⟩
    rw [fl_get I hp] at hI'
    rw [fl_get X hp] at hX'
    exact (land_ne_zero_iff hI hX).2 ⟨p, hp, hI', hX'⟩
  · intro hne
    obtain ⟨p, hp, hI', hX'⟩ := (land_ne_zero_iff hI hX).1 hne
    exact ⟨p, hp, by rw [fl_get I hp]; exact hI', by rw [fl_get X hp]; exact hX'⟩

theorem allIn_complete_iff {I X : Nat} (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    allIn 0 693 (fun p => (fl I)[p]! || (fl X)[p]!) = true ↔ I ||| X = 2 ^ 693 - 1 := by
  rw [allIn_iff']
  constructor
  · intro h
    exact (lor_eq_all_ones_iff hI hX).2 fun p hp => by
      have h1 := h p (Nat.zero_le _) hp
      rwa [fl_get I hp, fl_get X hp, Bool.or_eq_true] at h1
  · intro h p _ hp
    have h1 := (lor_eq_all_ones_iff hI hX).1 h p hp
    rw [fl_get I hp, fl_get X hp, Bool.or_eq_true]
    exact h1

private noncomputable def extBit (L e ih : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.lor ih (Nat.shiftLeft 1 (Nat.add 693 (e % 1024))))
    (Nat.lor ih (Nat.shiftLeft 1 (e % 1024)))
    (bitK L (e / 1024))

private noncomputable def extC (L e : Nat) : Nat :=
  if bitK L (e / 1024) = true then 2 ^ (e % 1024) else 2 ^ (693 + e % 1024)

private noncomputable def extK' (L : Nat) (l : List Nat) (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) S (fun e _ ih => extBit L e ih) l

private theorem extK_eq_extK' (LB : Nat → Nat) (NL : Nat → List Nat) (x j S : Nat) :
    extK LB NL x j S = extK' (LB j) (NL x) S := by
  unfold extK extK' extBit
  rw [letN_eq]
  rfl

private theorem extBit_eq (L e ih : Nat) : extBit L e ih = ih ||| extC L e := by
  unfold extBit extC
  simp only [Nat.shiftLeft_eq', Nat.one_shiftLeft]
  cases h : bitK L (e / 1024) <;> simp [h]

private theorem extC_lt (L e : Nat) (h : e % 1024 < 693) : extC L e < 2 ^ 1386 := by
  unfold extC
  split
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)

private theorem extBit_lt (L e : Nat) (h : e % 1024 < 693) :
    ∀ ih, ih < 2 ^ 1386 → extBit L e ih < 2 ^ 1386 := by
  intro ih hih
  rw [extBit_eq]
  exact Nat.or_lt_two_pow hih (extC_lt L e h)

private theorem extK'_lt (L : Nat) (l : List Nat) (h : ∀ e ∈ l, e % 1024 < 693) :
    ∀ S, S < 2 ^ 1386 → extK' L l S < 2 ^ 1386 := by
  induction l with
  | nil => intro S hS; simpa [extK'] using hS
  | cons a t ih =>
    intro S hS
    have ha : a % 1024 < 693 := h a (by simp)
    have ht : ∀ e ∈ t, e % 1024 < 693 := fun e he => h e (by simp [he])
    show extBit L a (extK' L t S) < 2 ^ 1386
    exact extBit_lt L a ha _ (ih ht S hS)

private theorem extBit_or (L e S d : Nat) : extBit L e (S ||| d) = S ||| extBit L e d := by
  rw [extBit_eq, extBit_eq, Nat.or_assoc]

private theorem extK'_or (L : Nat) (l : List Nat) (S : Nat) :
    extK' L l S = S ||| extK' L l 0 := by
  induction l with
  | nil => simp [extK']
  | cons a t ih =>
    show extBit L a (extK' L t S) = S ||| extBit L a (extK' L t 0)
    rw [ih]
    exact extBit_or L a S (extK' L t 0)

private theorem extK'_or_base (L : Nat) (l : List Nat) (S d : Nat) :
    extK' L l (S ||| d) = S ||| extK' L l d := by
  rw [extK'_or L l (S ||| d), extK'_or L l d, Nat.or_assoc]

theorem hypCand_extK_or (LB : Nat → Nat) (NL : Nat → List Nat) (x j S : Nat) :
    extK LB NL x j S = S ||| extK LB NL x j 0 := by
  rw [extK_eq_extK' LB NL x j S, extK'_or (LB j) (NL x) S, ← extK_eq_extK' LB NL x j 0]

private theorem extK'_zero_eq (L : Nat) (l : List Nat) :
    extK' L l 0 = List.rec (motive := fun _ => Nat) 0
      (fun e _ ih => Nat.lor ih (extC L e)) l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show extBit L a (extK' L t 0)
      = Nat.lor (List.rec (motive := fun _ => Nat) 0
          (fun e _ ih => Nat.lor ih (extC L e)) t) (extC L a)
    rw [extBit_eq, ih]
    rfl

private theorem testBit_rec_or (l : List Nat) (g : Nat → Nat) (p : Nat) :
    (List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.lor ih (g y)) l).testBit p
      = l.any (fun y => (g y).testBit p) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    show (Nat.lor (List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.lor ih (g y)) t)
      (g a)).testBit p = _
    rw [Nat.lor_eq, Nat.testBit_or, ih, List.any_cons, Bool.or_comm]

private theorem extK'_testBit (L : Nat) (l : List Nat) (S p : Nat) :
    (extK' L l S).testBit p = (S.testBit p || l.any (fun e => (extC L e).testBit p)) := by
  rw [extK'_or, Nat.testBit_or, extK'_zero_eq L l, testBit_rec_or]

private theorem testBit_ite_two_pow (c : Bool) (y p : Nat) :
    (if c then 2 ^ y else 0 : Nat).testBit p = (c && decide (y = p)) := by
  cases c <;> simp [Nat.testBit_two_pow]

private theorem testBit_ite_zero_two_pow (c : Bool) (y p : Nat) :
    (if c then 0 else 2 ^ y : Nat).testBit p = (!c && decide (y = p)) := by
  cases c <;> simp [Nat.testBit_two_pow]

private theorem set_fl (A y : Nat) (hy : y < 693) :
    (fl A).set! y true = fl (A ||| 2 ^ y) := by
  apply flags_eq
  · rw [Array.size_set!, fl_size]
  · intro p hp
    rw [Nat.testBit_or]
    by_cases hpy : p = y
    · subst hpy
      rw [Array.getElem!_set!_self _ _ _ (by rw [fl_size]; exact hy), Nat.testBit_two_pow]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hpy h.symm), fl_get A hp,
        Nat.testBit_two_pow, decide_eq_false (fun h => hpy h.symm)]
      simp

private theorem foldl_set_fl : ∀ (l : List Nat), (∀ y ∈ l, y < 693) →
    ∀ (c : Nat → Bool) (S : Nat),
      l.foldl (fun F y => if c y then F.set! y true else F) (fl S)
        = fl (l.foldl (fun acc y => acc ||| (if c y then 2 ^ y else 0)) S) := by
  intro l
  induction l with
  | nil => intro _ c S; simp
  | cons a t ih =>
    intro hl c S
    have ha : a < 693 := hl a (by simp)
    have ht : ∀ y ∈ t, y < 693 := fun y hy => hl y (by simp [hy])
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hc : c a = true
    · rw [if_pos hc, if_pos hc, set_fl S a ha]
      exact ih ht c (S ||| 2 ^ a)
    · rw [if_neg hc, if_neg hc, Nat.or_zero]
      exact ih ht c S

private theorem foldl_set_fl' : ∀ (l : List Nat), (∀ y ∈ l, y < 693) →
    ∀ (c : Nat → Bool) (S : Nat),
      l.foldl (fun F y => if c y then F else F.set! y true) (fl S)
        = fl (l.foldl (fun acc y => acc ||| (if c y then 0 else 2 ^ y)) S) := by
  intro l
  induction l with
  | nil => intro _ c S; simp
  | cons a t ih =>
    intro hl c S
    have ha : a < 693 := hl a (by simp)
    have ht : ∀ y ∈ t, y < 693 := fun y hy => hl y (by simp [hy])
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hc : c a = true
    · rw [if_pos hc, if_pos hc, Nat.or_zero]
      exact ih ht c S
    · rw [if_neg hc, if_neg hc, set_fl S a ha]
      exact ih ht c (S ||| 2 ^ a)

private theorem foldl_ite_congr (l : List Nat) (p q : Nat → Bool) (F0 : Flags)
    (h : ∀ y ∈ l, p y = q y) :
    l.foldl (fun F y => if p y then F.set! y true else F) F0
      = l.foldl (fun F y => if q y then F.set! y true else F) F0 := by
  induction l generalizing F0 with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons, List.foldl_cons, h a (by simp)]
    exact ih (if q a then F0.set! a true else F0) (fun y hy => h y (by simp [hy]))

private theorem foldl_ite_congr' (l : List Nat) (p q : Nat → Bool) (F0 : Flags)
    (h : ∀ y ∈ l, p y = q y) :
    l.foldl (fun F y => if p y then F else F.set! y true) F0
      = l.foldl (fun F y => if q y then F else F.set! y true) F0 := by
  induction l generalizing F0 with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons, List.foldl_cons, h a (by simp)]
    exact ih (if q a then F0 else F0.set! a true) (fun y hy => h y (by simp [hy]))

private theorem testBit_foldl_or (l : List Nat) (g : Nat → Nat) (S p : Nat) :
    (l.foldl (fun acc y => acc ||| g y) S).testBit p
      = (S.testBit p || l.any (fun y => (g y).testBit p)) := by
  induction l generalizing S with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

private theorem testBit_foldl_or' (l : List Nat) (g : Nat → Bool) (S p : Nat) :
    (l.foldl (fun acc y => if g y then acc else acc ||| 2 ^ y) S).testBit p
      = (S.testBit p || l.any (fun y => (!g y && decide (y = p)))) := by
  rw [show (fun acc y => if g y then acc else acc ||| 2 ^ y)
      = (fun acc y => acc ||| (if g y then 0 else 2 ^ y)) from by
        funext acc y; by_cases h : g y = true <;> simp [h]]
  rw [testBit_foldl_or]
  congr 1
  exact List.any_congr rfl (fun y => testBit_ite_zero_two_pow (g y) y p)

private theorem any_congr_mem (l : List Nat) {p q : Nat → Bool} (h : ∀ y ∈ l, p y = q y) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.any_cons, List.any_cons, h a (by simp)]
    rw [ih fun y hy => h y (by simp [hy])]

private theorem extC_testBit_low (L y g p : Nat) (hy : y < 693) (hg : g < 693)
    (hp : p < 693) :
    (extC L (y + 1024 * g)).testBit p = (bitK L g && decide (y = p)) := by
  unfold extC
  have hmod : (y + 1024 * g) % 1024 = y := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (y + 1024 * g) / 1024 = g := by
    rw [Nat.add_mul_div_left y g (by norm_num), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [hmod, hdiv]
  have hne : ¬ (693 + y = p) := by omega
  cases h : bitK L g
  · simp [Nat.testBit_two_pow, decide_eq_false hne]
  · simp [Nat.testBit_two_pow]

private theorem extC_testBit_high (L y g p : Nat) (hy : y < 693) (hg : g < 693)
    (hp : p < 693) :
    (extC L (y + 1024 * g)).testBit (693 + p) = (!bitK L g && decide (y = p)) := by
  unfold extC
  have hmod : (y + 1024 * g) % 1024 = y := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (y + 1024 * g) / 1024 = g := by
    rw [Nat.add_mul_div_left y g (by norm_num), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [hmod, hdiv]
  have hne : ¬ (y = 693 + p) := by omega
  cases h : bitK L g
  · simp [Nat.testBit_two_pow, decide_eq_decide.mpr Nat.add_left_cancel_iff]
  · simp [Nat.testBit_two_pow, decide_eq_false hne]

private noncomputable def candK' (LI : Nat → Nat) (S I : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (2 ^ 1024 - 1)
    (fun e _ ih => Bool.rec (motive := fun _ => Nat) ih
      (letN (liAt LI (e / 1024)) fun Ly => Bool.rec (motive := fun _ => Nat)
        (Nat.land ih (Nat.xor Ly (2 ^ 1024 - 1))) (Nat.land ih Ly)
        (bitK I (e % 1024)))
      (bitK S (e % 1024))) l

private theorem candK_eq_candK' (LI : Nat → Nat) (NL : Nat → List Nat) (x I X : Nat) :
    candK LI NL x I X = candK' LI (I ||| X) I (NL x) := by
  unfold candK candK'
  rw [letN_eq]
  simp only [Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rfl

private theorem candK'_lt (LI : Nat → Nat) (S I : Nat) (l : List Nat) :
    candK' LI S I l < 2 ^ 1024 := by
  induction l with
  | nil =>
    show 2 ^ 1024 - 1 < 2 ^ 1024
    exact Nat.sub_lt (Nat.two_pow_pos 1024) (by norm_num)
  | cons a t ih =>
    show (Bool.rec (motive := fun _ => Nat) (candK' LI S I t)
      (letN (liAt LI (a / 1024)) fun Ly => Bool.rec (motive := fun _ => Nat)
        (Nat.land (candK' LI S I t) (Nat.xor Ly (2 ^ 1024 - 1)))
        (Nat.land (candK' LI S I t) Ly) (bitK I (a % 1024)))
      (bitK S (a % 1024))) < 2 ^ 1024
    simp only [letN_eq]
    cases h1 : bitK S (a % 1024)
    · exact ih
    · cases h2 : bitK I (a % 1024)
      · exact lt_of_le_of_lt Nat.and_le_left ih
      · exact lt_of_le_of_lt Nat.and_le_left ih

private theorem testBit_xor_mask (Ly j : Nat) (hj : j < 1024) :
    (Ly ^^^ (2 ^ 1024 - 1)).testBit j = !(Ly.testBit j) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hj, Bool.xor_true]

private theorem candStep_testBit (LI : Nat → Nat) (S I e ih j : Nat) (hj : j < 1024) :
    (Bool.rec (motive := fun _ => Nat) ih
      (letN (liAt LI (e / 1024)) fun Ly => Bool.rec (motive := fun _ => Nat)
        (Nat.land ih (Nat.xor Ly (2 ^ 1024 - 1))) (Nat.land ih Ly)
        (bitK I (e % 1024)))
      (bitK S (e % 1024))).testBit j = true ↔
      ((bitK S (e % 1024) = false) ∨
        (bitK I (e % 1024) = true ∧ (liAt LI (e / 1024)).testBit j = true) ∨
        (bitK I (e % 1024) = false ∧ (liAt LI (e / 1024)).testBit j = false)) ∧
      ih.testBit j = true := by
  simp only [letN_eq]
  cases h1 : bitK S (e % 1024)
  · simp [h1]
  · cases h2 : bitK I (e % 1024)
    · dsimp only
      rw [Nat.land_eq, Nat.testBit_and, Nat.xor_eq, testBit_xor_mask _ _ hj]
      simp [h1, h2]
      tauto
    · dsimp only
      rw [Nat.land_eq, Nat.testBit_and]
      simp [h1, h2]
      tauto

private theorem candK'_testBit (LI : Nat → Nat) (S I : Nat) (l : List Nat) (j : Nat)
    (hj : j < 1024) :
    (candK' LI S I l).testBit j = true ↔
      ∀ e ∈ l, (bitK S (e % 1024) = false) ∨
        (bitK I (e % 1024) = true ∧ (liAt LI (e / 1024)).testBit j = true) ∨
        (bitK I (e % 1024) = false ∧ (liAt LI (e / 1024)).testBit j = false) := by
  induction l with
  | nil =>
    rw [show candK' LI S I [] = 2 ^ 1024 - 1 from rfl, Nat.testBit_two_pow_sub_one,
      decide_eq_true hj]
    simp
  | cons a t ih =>
    rw [show candK' LI S I (a :: t) = Bool.rec (motive := fun _ => Nat) (candK' LI S I t)
      (letN (liAt LI (a / 1024)) fun Ly => Bool.rec (motive := fun _ => Nat)
        (Nat.land (candK' LI S I t) (Nat.xor Ly (2 ^ 1024 - 1)))
        (Nat.land (candK' LI S I t) Ly) (bitK I (a % 1024)))
      (bitK S (a % 1024)) from rfl,
      candStep_testBit LI S I a (candK' LI S I t) j hj]
    rw [ih, List.forall_mem_cons]

private theorem cand_clause (i x r : Bool) (h : (i && x) = false) :
    (((i || x) = false) ∨ (i = true ∧ r = true) ∨ (i = false ∧ r = false)) ↔
      ((i = true → r = true) ∧ (x = true → r = false)) := by
  cases i <;> cases x <;> cases r <;> simp_all

private theorem lam_testBit_eq (hC : SearchCtx C PB LB LI GI PL NL) {j a : Nat}
    (hj : j < 1024) (ha : a < 693) : (C.lam[j]!)[a]! = (liAt LI a).testBit j := by
  rw [hC.lam j hj, fl_get (LB j) ha, hC.li a ha j hj]

private theorem pair_mod (y g : Nat) (hy : y < 1024) : (y + 1024 * g) % 1024 = y := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]

private theorem pair_div (y g : Nat) (hy : y < 1024) : (y + 1024 * g) / 1024 = g := by
  rw [Nat.add_mul_div_left y g (by norm_num), Nat.div_eq_of_lt hy, Nat.zero_add]

private theorem candClause_iff (x : Nat) {I X y j : Nat} (hIX : I &&& X = 0) (hy : y < 693) :
    ((bitK (I ||| X) y = false) ∨
      (bitK I y = true ∧ (liAt LI (fd 10 (GI x) y)).testBit j = true) ∨
      (bitK I y = false ∧ (liAt LI (fd 10 (GI x) y)).testBit j = false))
    ↔ ((I.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = true) ∧
       (X.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = false)) := by
  have hix : (I.testBit y && X.testBit y) = false := by
    have h := congrArg (fun n => n.testBit y) hIX
    rwa [Nat.testBit_and, Nat.zero_testBit] at h
  rw [bitK_eq_testBit, bitK_eq_testBit, Nat.testBit_or]
  exact cand_clause (I.testBit y) (X.testBit y) ((liAt LI (fd 10 (GI x) y)).testBit j) hix

private theorem candK'_testBit_nl (hC : SearchCtx C PB LB LI GI PL NL) {x I X j : Nat}
    (hx : x < 693) (hj : j < 1024) (hIX : I &&& X = 0) :
    (candK' LI (I ||| X) I (NL x)).testBit j = true ↔
      (∀ y ∈ PL x, I.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = true) ∧
      (∀ y ∈ PL x, X.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = false) := by
  rw [candK'_testBit LI (I ||| X) I (NL x) j hj, hC.nl x hx, List.forall_mem_map]
  constructor
  · intro h
    refine ⟨fun y hy hit => ?_, fun y hy hit => ?_⟩
    · have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
      have hcl := h y hy
      rw [pair_mod y _ (by omega), pair_div y _ (by omega)] at hcl
      exact ((candClause_iff x hIX hy693).1 hcl).1 hit
    · have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
      have hcl := h y hy
      rw [pair_mod y _ (by omega), pair_div y _ (by omega)] at hcl
      exact ((candClause_iff x hIX hy693).1 hcl).2 hit
  · rintro ⟨hA, hB⟩ y hy
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    rw [pair_mod y _ (by omega), pair_div y _ (by omega)]
    exact (candClause_iff x hIX hy693).2 ⟨fun hit => hA y hy hit, fun hit => hB y hy hit⟩

private theorem mem_candA (hC : SearchCtx C PB LB LI GI PL NL) {I x a : Nat} (hx : x < 693) :
    a ∈ (PL x).toArray.filterMap
        (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)
      ↔ ∃ y ∈ PL x, I.testBit y = true ∧ fd 10 (GI x) y = a := by
  rw [Array.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    have hy' : y ∈ PL x := by simpa using hy
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy').1
    by_cases hit : (fl I)[y]! = true
    · rw [if_pos hit] at h
      simp only [Option.some.injEq] at h
      exact ⟨y, hy', by rwa [fl_get I hy693] at hit,
        by rw [← ((hC.gI x hx).2 y hy693).1]; exact h⟩
    · rw [if_neg hit] at h
      simp at h
  · rintro ⟨y, hy, hit, hay⟩
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    refine ⟨y, by simpa using hy, ?_⟩
    rw [if_pos (by rwa [fl_get I hy693]), ((hC.gI x hx).2 y hy693).1]
    exact congrArg some hay

private theorem mem_candB (hC : SearchCtx C PB LB LI GI PL NL) {X x b : Nat} (hx : x < 693) :
    b ∈ (PL x).toArray.filterMap
        (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)
      ↔ ∃ y ∈ PL x, X.testBit y = true ∧ fd 10 (GI x) y = b := by
  rw [Array.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    have hy' : y ∈ PL x := by simpa using hy
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy').1
    by_cases hit : (fl X)[y]! = true
    · rw [if_pos hit] at h
      simp only [Option.some.injEq] at h
      exact ⟨y, hy', by rwa [fl_get X hy693] at hit,
        by rw [← ((hC.gI x hx).2 y hy693).1]; exact h⟩
    · rw [if_neg hit] at h
      simp at h
  · rintro ⟨y, hy, hit, hay⟩
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    refine ⟨y, by simpa using hy, ?_⟩
    rw [if_pos (by rwa [fl_get X hy693]), ((hC.gI x hx).2 y hy693).1]
    exact congrArg some hay

private theorem all_candA {I j : Nat} (hC : SearchCtx C PB LB LI GI PL NL) {x : Nat}
    (hx : x < 693) (hj : j < 1024) :
    ((PL x).toArray.filterMap
        (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
        (fun a => (C.lam[j]!)[a]!) = true ↔
      ∀ y ∈ PL x, I.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h y hy hit
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    have hay : fd 10 (GI x) y ∈ (PL x).toArray.filterMap
        (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none) :=
      (mem_candA hC hx).2 ⟨y, hy, hit, rfl⟩
    have h1 := h _ hay
    rwa [lam_testBit_eq hC hj ((hC.gI x hx).2 y hy693).2] at h1
  · intro h a ha
    obtain ⟨y, hy, hit, hay⟩ := (mem_candA hC hx).1 ha
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    rw [← hay, lam_testBit_eq hC hj ((hC.gI x hx).2 y hy693).2]
    exact h y hy hit

private theorem all_candB {X j : Nat} (hC : SearchCtx C PB LB LI GI PL NL) {x : Nat}
    (hx : x < 693) (hj : j < 1024) :
    ((PL x).toArray.filterMap
        (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
        (fun b => !((C.lam[j]!)[b]!)) = true ↔
      ∀ y ∈ PL x, X.testBit y = true → (liAt LI (fd 10 (GI x) y)).testBit j = false := by
  rw [Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h y hy hit
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    have hay : fd 10 (GI x) y ∈ (PL x).toArray.filterMap
        (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none) :=
      (mem_candB hC hx).2 ⟨y, hy, hit, rfl⟩
    have h1 := h _ hay
    rw [lam_testBit_eq hC hj ((hC.gI x hx).2 y hy693).2] at h1
    simpa using h1
  · intro h b hb
    obtain ⟨y, hy, hit, hay⟩ := (mem_candB hC hx).1 hb
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    rw [← hay, lam_testBit_eq hC hj ((hC.gI x hx).2 y hy693).2]
    have h1 := h y hy hit
    simpa using h1

theorem candK_spec (hC : SearchCtx C PB LB LI GI PL NL) {x I X : Nat} (hx : x < 693)
    (hIX : I &&& X = 0) :
    candK LI NL x I X < 2 ^ 1024 ∧
      cands C x (fl I) (fl X) =
        (List.range 1024).filter fun j => (candK LI NL x I X).testBit j := by
  have hbound : candK LI NL x I X < 2 ^ 1024 := by
    rw [candK_eq_candK']
    exact candK'_lt LI (I ||| X) I (NL x)
  refine ⟨hbound, ?_⟩
  have hunfold : cands C x (fl I) (fl X) =
      (match ((PL x).toArray.filterMap
          (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).find? (· != 0) with
       | some a => C.lamIdx[a]!
       | none => List.range 1024).filter
        (fun j => ((PL x).toArray.filterMap
              (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
              (fun a => (C.lam[j]!)[a]!) &&
          ((PL x).toArray.filterMap
              (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
              (fun b => !((C.lam[j]!)[b]!))) := by
    unfold cands
    rw [hC.pl x hx]
    dsimp only
    rfl
  rw [hunfold]
  have hcond : ∀ j < 1024,
      (((PL x).toArray.filterMap
          (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
          (fun a => (C.lam[j]!)[a]!) &&
        ((PL x).toArray.filterMap
          (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
          (fun b => !((C.lam[j]!)[b]!))) =
      (candK LI NL x I X).testBit j := by
    intro j hj
    apply Bool.eq_iff_iff.mpr
    rw [Bool.and_eq_true, all_candA hC hx hj, all_candB hC hx hj,
      candK_eq_candK', candK'_testBit_nl hC hx hj hIX]
  cases hfind : ((PL x).toArray.filterMap
      (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).find? (· != 0) with
  | none =>
    dsimp only
    exact List.filter_congr (fun j hj => hcond j (List.mem_range.1 hj))
  | some a =>
    dsimp only
    have ha_mem : a ∈ (PL x).toArray.filterMap
        (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none) :=
      Array.mem_of_find?_eq_some hfind
    obtain ⟨y, hy, -, hay⟩ := (mem_candA hC hx).1 ha_mem
    have ha_lt : a < 693 := by
      rw [← hay]
      exact ((hC.gI x hx).2 y (((hC.mem_PL x hx y).1 hy).1)).2
    have hlamIdx : C.lamIdx[a]! = (List.range 1024).filter
        (fun j => (liAt LI a).testBit j) := by
      rw [hC.lamIdx a ha_lt, filterRange_eq, List.append_nil]
      apply List.filter_congr
      intro j hj
      exact lam_testBit_eq hC (List.mem_range.1 hj) ha_lt
    rw [hlamIdx, List.filter_filter]
    refine List.filter_congr (fun j hj => ?_)
    have hj1024 : j < 1024 := List.mem_range.1 hj
    have hpp : ((((PL x).toArray.filterMap
            (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
            (fun a => (C.lam[j]!)[a]!) &&
          ((PL x).toArray.filterMap
            (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
            (fun b => !((C.lam[j]!)[b]!))) && (liAt LI a).testBit j)
        = (((PL x).toArray.filterMap
            (fun y => if (fl I)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
            (fun a => (C.lam[j]!)[a]!) &&
          ((PL x).toArray.filterMap
            (fun y => if (fl X)[y]! = true then some (ap (C.gI[x]!) y) else none)).all
            (fun b => !((C.lam[j]!)[b]!))) := by
      rw [Bool.and_eq_left_iff_imp]
      intro hp
      have hA := (Array.all_eq_true_iff_forall_mem.1 (Bool.and_eq_true_iff.1 hp).1) a ha_mem
      rwa [lam_testBit_eq hC hj1024 ha_lt] at hA
    rw [hpp, hcond j hj1024]


theorem extK_spec (hC : SearchCtx C PB LB LI GI PL NL) {x j I X : Nat} (hx : x < 693)
    (hj : j < 1024) (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    extK LB NL x j (I ||| X <<< 693) < 2 ^ 1386 ∧
      extI C [(x, j)] (fl I) = fl (extK LB NL x j (I ||| X <<< 693) &&& (2 ^ 693 - 1)) ∧
      extX C [(x, j)] (fl X) = fl (extK LB NL x j (I ||| X <<< 693) >>> 693) := by
  have hS0lt : I ||| X <<< 693 < 2 ^ 1386 := by
    have hI' : I < 2 ^ 1386 :=
      lt_of_lt_of_le hI (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    refine Nat.or_lt_two_pow (n := 1386) hI' ?_
    rw [Nat.shiftLeft_eq]
    calc X * 2 ^ 693 < 2 ^ 693 * 2 ^ 693 :=
          Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos 693)
      _ = 2 ^ 1386 := by rw [← Nat.pow_add]
  have hlow : ∀ e ∈ NL x, e % 1024 < 693 := by
    intro e he
    rw [hC.nl x hx] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    exact hy693
  have hcond : ∀ y ∈ PL x, (C.lam[j]!)[ap (C.gI[x]!) y]! = bitK (LB j) (fd 10 (GI x) y) := by
    intro y hy
    have hy693 : y < 693 := ((hC.mem_PL x hx y).1 hy).1
    have hgy : ap (C.gI[x]!) y = fd 10 (GI x) y := ((hC.gI x hx).2 y hy693).1
    have hgylt : fd 10 (GI x) y < 693 := ((hC.gI x hx).2 y hy693).2
    rw [hgy, hC.lam j hj, fl_get (LB j) hgylt, bitK_eq_testBit]
  refine ⟨?_, ?_, ?_⟩
  · rw [extK_eq_extK', extK'_or]
    exact Nat.or_lt_two_pow hS0lt (extK'_lt (LB j) (NL x) hlow 0 (Nat.two_pow_pos 1386))
  · have hunfold : extI C [(x, j)] (fl I) =
        (PL x).foldl (fun F y =>
          if (C.lam[j]!)[ap (C.gI[x]!) y]! then F.set! y true else F) (fl I) := by
      unfold extI
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hC.pl x hx, List.foldl_toArray]
    have hstep : (PL x).foldl (fun F y =>
            if (C.lam[j]!)[ap (C.gI[x]!) y]! then F.set! y true else F) (fl I)
        = (PL x).foldl (fun F y =>
            if bitK (LB j) (fd 10 (GI x) y) then F.set! y true else F) (fl I) :=
      foldl_ite_congr (PL x) _ _ (fl I) (fun y hy => hcond y hy)
    have hfl := foldl_set_fl (PL x) (fun y hy => ((hC.mem_PL x hx y).1 hy).1)
      (fun y => bitK (LB j) (fd 10 (GI x) y)) I
    have hLtest : ∀ p < 693, ((PL x).foldl (fun acc y =>
            acc ||| (if bitK (LB j) (fd 10 (GI x) y) then 2 ^ y else 0)) I).testBit p
        = (I.testBit p || (PL x).any (fun y =>
            bitK (LB j) (fd 10 (GI x) y) && decide (y = p))) := by
      intro p hp
      rw [testBit_foldl_or]
      rw [List.any_congr rfl (fun y => testBit_ite_two_pow (bitK (LB j) (fd 10 (GI x) y)) y p)]
    have hRtest : ∀ p < 693, (extK LB NL x j (I ||| X <<< 693)).testBit p
        = (I.testBit p || (PL x).any (fun y =>
            bitK (LB j) (fd 10 (GI x) y) && decide (y = p))) := by
      intro p hp
      rw [extK_eq_extK', extK'_testBit, hC.nl x hx, List.any_map]
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have hpge : ¬ (p ≥ 693) := by omega
      rw [decide_eq_false hpge, Bool.false_and, Bool.or_false]
      exact congrArg (fun z => I.testBit p || z)
        (any_congr_mem (PL x) (fun y hy => extC_testBit_low (LB j) y (fd 10 (GI x) y) p
          (((hC.mem_PL x hx y).1 hy).1)
          (((hC.gI x hx).2 y (((hC.mem_PL x hx y).1 hy).1)).2) hp))
    have hflag : fl ((PL x).foldl (fun acc y =>
            acc ||| (if bitK (LB j) (fd 10 (GI x) y) then 2 ^ y else 0)) I)
        = fl (extK LB NL x j (I ||| X <<< 693) &&& (2 ^ 693 - 1)) := by
      apply flags_eq
      · rw [fl_size]
      · intro p hp
        rw [fl_get _ hp, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
          decide_eq_true hp, Bool.and_true]
        rw [hLtest p hp, hRtest p hp]
    exact hunfold.trans (hstep.trans (hfl.trans hflag))
  · have hunfold : extX C [(x, j)] (fl X) =
        (PL x).foldl (fun F y =>
          if (C.lam[j]!)[ap (C.gI[x]!) y]! then F else F.set! y true) (fl X) := by
      unfold extX
      simp only [List.foldl_cons, List.foldl_nil]
      rw [hC.pl x hx, List.foldl_toArray]
    have hstep : (PL x).foldl (fun F y =>
            if (C.lam[j]!)[ap (C.gI[x]!) y]! then F else F.set! y true) (fl X)
        = (PL x).foldl (fun F y =>
            if bitK (LB j) (fd 10 (GI x) y) then F else F.set! y true) (fl X) :=
      foldl_ite_congr' (PL x) _ _ (fl X) (fun y hy => hcond y hy)
    have hfl := foldl_set_fl' (PL x) (fun y hy => ((hC.mem_PL x hx y).1 hy).1)
      (fun y => bitK (LB j) (fd 10 (GI x) y)) X
    have hLtest : ∀ p < 693, ((PL x).foldl (fun acc y =>
            acc ||| (if bitK (LB j) (fd 10 (GI x) y) then 0 else 2 ^ y)) X).testBit p
        = (X.testBit p || (PL x).any (fun y =>
            !(bitK (LB j) (fd 10 (GI x) y)) && decide (y = p))) := by
      intro p hp
      rw [testBit_foldl_or]
      rw [List.any_congr rfl (fun y => testBit_ite_zero_two_pow (bitK (LB j) (fd 10 (GI x) y)) y p)]
    have hRtest : ∀ p < 693, (extK LB NL x j (I ||| X <<< 693) >>> 693).testBit p
        = (X.testBit p || (PL x).any (fun y =>
            !(bitK (LB j) (fd 10 (GI x) y)) && decide (y = p))) := by
      intro p hp
      rw [Nat.testBit_shiftRight]
      rw [extK_eq_extK', extK'_testBit, hC.nl x hx, List.any_map]
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      rw [decide_eq_true (by omega : 693 + p ≥ 693), Bool.true_and]
      have hIlt : I.testBit (693 + p) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hI
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hIlt, Bool.false_or]
      rw [show 693 + p - 693 = p from by omega]
      exact congrArg (fun z => X.testBit p || z)
        (any_congr_mem (PL x) (fun y hy => extC_testBit_high (LB j) y (fd 10 (GI x) y) p
          (((hC.mem_PL x hx y).1 hy).1)
          (((hC.gI x hx).2 y (((hC.mem_PL x hx y).1 hy).1)).2) hp))
    have hflag : fl ((PL x).foldl (fun acc y =>
            acc ||| (if bitK (LB j) (fd 10 (GI x) y) then 0 else 2 ^ y)) X)
        = fl (extK LB NL x j (I ||| X <<< 693) >>> 693) := by
      apply flags_eq
      · rw [fl_size]
      · intro p hp
        rw [fl_get _ hp, hLtest p hp, hRtest p hp]
    exact hunfold.trans (hstep.trans (hfl.trans hflag))

end CFSG.KC.Misc.Hyp

end
