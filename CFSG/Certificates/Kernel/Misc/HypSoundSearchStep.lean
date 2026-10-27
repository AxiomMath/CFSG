module

public import CFSG.Certificates.Kernel.Misc.HypSoundSearchCand
public import CFSG.Certificates.Kernel.Misc.HypSoundSearchBits
public import Certificates.Data.Kernel.Misc.HypRun

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

variable {C : HCtx} {PB LB LI GI : Nat → Nat} {PL NL : Nat → List Nat}

private theorem compl_testBit {I X y : Nat} (hy : y < 693) :
    (Nat.xor (Nat.lor I X) (2 ^ 693 - 1)).testBit y = !(I.testBit y || X.testBit y) := by
  simp only [Nat.xor_eq, Nat.lor_eq, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_sub_one,
    decide_eq_true hy]
  cases I.testBit y <;> cases X.testBit y <;> rfl

private theorem ne_zero_iff_testBit (n : Nat) : n ≠ 0 ↔ ∃ i, n.testBit i = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩ h
    rw [h] at hi
    simp at hi

private theorem land_ne_zero_iff (a b : Nat) :
    a &&& b ≠ 0 ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_land] at hi
    exact ⟨i, (Bool.and_eq_true_iff.mp hi).1, (Bool.and_eq_true_iff.mp hi).2⟩
  · rintro ⟨i, ha, hb⟩
    exact fun h0 => by
      have : (a &&& b).testBit i = true := by rw [Nat.testBit_land, ha, hb]; rfl
      rw [h0] at this
      simp at this

private theorem not_beq_zero (n : Nat) : (!(Nat.beq n 0)) = decide (n ≠ 0) := by
  cases n <;> rfl

private theorem not_beq_zero_eq_true (n : Nat) : (!(Nat.beq n 0)) = true ↔ n ≠ 0 := by
  rw [show Nat.beq n 0 = decide (n = 0) from rfl, ← decide_not, decide_eq_true_eq]

private noncomputable def openB (PB : Nat → Nat) (x I X : Nat) : Bool :=
  andB (bitK I x) (notB (Nat.beq (Nat.land (PB x)
    (Nat.xor (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1))) 0))

private def openF (C : HCtx) (I X : Flags) (x : Nat) : Bool :=
  I[x]! && C.pl[x]!.any (fun y => !(I[y]! || X[y]!))

private theorem openB_eq_openF (hC : SearchCtx C PB LB LI GI PL NL) {x I X : Nat}
    (hx : x < 693) (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    openB PB x I X = openF C (fl I) (fl X) x := by
  have hany : C.pl[x]!.any (fun y => !((fl I)[y]! || (fl X)[y]!)) = true ↔
      Nat.land (PB x) (Nat.xor (Nat.lor I X) (2 ^ 693 - 1)) ≠ 0 := by
    rw [hC.pl x hx, ← Array.any_toList, List.toList_toArray, List.any_eq_true]
    constructor
    · rintro ⟨y, hy, hfy⟩
      obtain ⟨hy693, hyb⟩ := (hC.mem_PL x hx y).1 hy
      rw [fl_get I hy693, fl_get X hy693] at hfy
      exact (land_ne_zero_iff (PB x) _).2
        ⟨y, hyb, by rw [compl_testBit hy693]; exact hfy⟩
    · intro h
      obtain ⟨y, hyb, hU⟩ := (land_ne_zero_iff (PB x) _).1 h
      have hy693 : y < 693 := lt_of_testBit (hC.PB_lt x hx) hyb
      refine ⟨y, (hC.mem_PL x hx y).2 ⟨hy693, hyb⟩, ?_⟩
      rw [fl_get I hy693, fl_get X hy693]
      rw [compl_testBit hy693] at hU
      exact hU
  apply Bool.eq_iff_iff.2
  unfold openB openF
  rw [andB_eq, bitK_eq_testBit, fl_get I hx, Bool.and_eq_true_iff, Bool.and_eq_true_iff,
    notB_eq, not_beq_zero_eq_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hany.mpr h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, hany.mp h2⟩

private def openP (C : HCtx) (I X : Flags) (n : Nat) : List Nat :=
  (List.range n).filter (openF C I X)

private def candP (C : HCtx) (I X : Flags) (n : Nat) : List (Nat × List Nat) :=
  (openP C I X n).map fun x => (x, cands C x I X)

private def forcedP (C : HCtx) (I X : Flags) (n : Nat) : List (Nat × Nat) :=
  forcedOf (candP C I X n)

private theorem openP_succ (C : HCtx) (I X : Flags) (n : Nat) :
    openP C I X (n + 1) = openP C I X n ++ (if openF C I X n then [n] else []) := by
  unfold openP
  rw [List.range_succ, List.filter_append]
  by_cases h : openF C I X n = true <;> simp [h]

private theorem candP_succ (C : HCtx) (I X : Flags) (n : Nat) :
    candP C I X (n + 1) =
      candP C I X n ++ (if openF C I X n then [(n, cands C n I X)] else []) := by
  unfold candP
  rw [openP_succ, List.map_append]
  by_cases h : openF C I X n = true <;> simp [h]

private theorem forcedP_succ (C : HCtx) (I X : Flags) (n : Nat) :
    forcedP C I X (n + 1) =
      forcedP C I X n ++ (if openF C I X n then forcedOf [(n, cands C n I X)] else []) := by
  unfold forcedP
  rw [candP_succ]
  unfold forcedOf
  rw [List.filterMap_append]
  by_cases h : openF C I X n = true <;> simp [h]

private theorem candsAt_eq_candP (C : HCtx) (I X : Flags) :
    candsAt C I X = candP C I X 693 := by
  unfold candsAt candP openP openPts openF
  rw [CFSG.KC.Misc.Xi.filterRange_eq, List.append_nil]

private theorem forcedOf_candsAt (C : HCtx) (I X : Flags) :
    forcedOf (candsAt C I X) = forcedP C I X 693 := by
  rw [candsAt_eq_candP]; rfl

private theorem cands_eq_filter (hC : SearchCtx C PB LB LI GI PL NL) {x I X : Nat}
    (hx : x < 693) (hIX : I &&& X = 0) :
    cands C x (fl I) (fl X) =
      (List.range 1024).filter (fun j => (candK LI NL x I X).testBit j) :=
  (candK_spec hC hx hIX).2

private theorem isEmpty_eq_false {α : Type} {l : List α} : (l.isEmpty = false) ↔ l ≠ [] := by
  cases l <;> simp

private theorem cands_isEmpty_eq (hC : SearchCtx C PB LB LI GI PL NL) {x I X : Nat}
    (hx : x < 693) (hIX : I &&& X = 0) :
    (cands C x (fl I) (fl X)).isEmpty = (candK LI NL x I X == 0) := by
  have hspec := candK_spec hC hx hIX
  rw [hspec.2]
  change ((List.range 1024).filter (fun j => (candK LI NL x I X).testBit j)).isEmpty
    = Nat.beq (candK LI NL x I X) 0
  by_cases h0 : candK LI NL x I X = 0
  · rw [h0]
    have : (List.range 1024).filter (fun j => (0 : Nat).testBit j) = [] := by simp
    rw [this]; simp
  · have hne : (List.range 1024).filter (fun j => (candK LI NL x I X).testBit j) ≠ [] :=
      fun he => h0 ((range_filter_testBit_eq_nil hspec.1).1 he)
    have hb : (Nat.beq (candK LI NL x I X) 0) = false := by
      cases hh : Nat.beq (candK LI NL x I X) 0 with
      | false => rfl
      | true =>
        rw [Nat.beq_eq] at hh
        exact absurd hh h0
    rw [hb]
    exact isEmpty_eq_false.2 hne

private theorem cands_eq_singleton_val (hC : SearchCtx C PB LB LI GI PL NL) {x I X j : Nat}
    (hx : x < 693) (hIX : I &&& X = 0) (hj : j < 1024) :
    cands C x (fl I) (fl X) = [j] ↔ candK LI NL x I X = 2 ^ j := by
  rw [cands_eq_filter hC hx hIX]
  exact range_filter_testBit_eq_singleton (candK_spec hC hx hIX).1

private theorem two_pow_and_pred (j : Nat) : (2 ^ j : Nat) &&& Nat.sub (2 ^ j) 1 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit, Nat.testBit_land, Nat.testBit_two_pow]
  by_cases hij : j = i
  · rw [decide_eq_true hij, Bool.true_and]
    rw [Nat.testBit_lt_two_pow (show Nat.sub (2 ^ j) 1 < 2 ^ i by
      rw [hij]; exact Nat.sub_lt (Nat.two_pow_pos i) (by norm_num))]
  · simp [hij]

private theorem shiftLeft_one_eq (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n :=
  Nat.one_shiftLeft n

private theorem cands_singleton_iff (hC : SearchCtx C PB LB LI GI PL NL) {x I X : Nat}
    (hx : x < 693) (hIX : I &&& X = 0) :
    (∃ j, cands C x (fl I) (fl X) = [j]) ↔
      candK LI NL x I X ≠ 0 ∧
        Nat.land (candK LI NL x I X) (Nat.sub (candK LI NL x I X) 1) = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    have hmem : j ∈ (List.range 1024).filter
        (fun i => (candK LI NL x I X).testBit i) := by
      rw [← cands_eq_filter hC hx hIX, hj]
      exact List.mem_singleton_self j
    have hjl : j < 1024 := List.mem_range.1 (List.mem_of_mem_filter hmem)
    have hpow : candK LI NL x I X = 2 ^ j :=
      (cands_eq_singleton_val hC hx hIX hjl).1 hj
    refine ⟨by rw [hpow]; positivity, ?_⟩
    rw [hpow, Nat.land_eq, two_pow_and_pred j]
  · rintro ⟨hne, hland⟩
    obtain ⟨j, hj⟩ := (land_sub_one_eq_zero_iff hne).1 hland
    have hjlt : j < 1024 := by
      by_contra hlt
      have hle : 2 ^ 1024 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hlt)
      rw [← hj] at hle
      exact (not_le_of_gt (candK_spec hC hx hIX).1) hle
    exact ⟨j, (cands_eq_singleton_val hC hx hIX hjlt).2 hj⟩

private theorem forcedOf_pair (n : Nat) (l : List Nat) :
    forcedOf [(n, l)] = match l with
      | [j] => [(n, j)]
      | _ => [] := by
  unfold forcedOf
  cases l with
  | nil => rfl
  | cons j t => cases t <;> rfl

private theorem listrec_or (step : Nat → Nat → Nat)
    (hstep : ∀ e S, step e S = S ||| step e 0) (L : List Nat) (S : Nat) :
    List.rec (motive := fun _ => Nat) S (fun e _ ih => step e ih) L =
      S ||| List.rec (motive := fun _ => Nat) 0 (fun e _ ih => step e ih) L := by
  induction L generalizing S with
  | nil => simp
  | cons e t ih =>
    change step e (List.rec (motive := fun _ => Nat) S (fun e _ ih => step e ih) t) =
      S ||| step e (List.rec (motive := fun _ => Nat) 0 (fun e _ ih => step e ih) t)
    rw [ih S, hstep e (S ||| List.rec (motive := fun _ => Nat) 0 (fun e _ ih => step e ih) t),
      hstep e (List.rec (motive := fun _ => Nat) 0 (fun e _ ih => step e ih) t), Nat.or_assoc]

private theorem extK_or (LB : Nat → Nat) (NL : Nat → List Nat) (x j S : Nat) :
    extK LB NL x j S = S ||| extK LB NL x j 0 := by
  unfold extK
  rw [letN_eq, letN_eq]
  refine listrec_or (L := NL x) (S := S)
    (fun e ih => Bool.rec (motive := fun _ => Nat)
      (Nat.lor ih (Nat.shiftLeft 1 (Nat.add 693 (Nat.mod e 1024))))
      (Nat.lor ih (Nat.shiftLeft 1 (Nat.mod e 1024)))
      (bitK (LB j) (Nat.div e 1024))) (fun e S => ?_)
  cases bitK (LB j) (Nat.div e 1024) <;>
    simp only [Nat.lor_eq, Nat.zero_or]

private theorem extI_append (C : HCtx) (F G : List (Nat × Nat)) (I : Flags) :
    extI C (F ++ G) I = extI C G (extI C F I) := by
  unfold extI
  rw [List.foldl_append]

private theorem extX_append (C : HCtx) (F G : List (Nat × Nat)) (X : Flags) :
    extX C (F ++ G) X = extX C G (extX C F X) := by
  unfold extX
  rw [List.foldl_append]

private theorem pow_and_mask_eq_zero {a b : Nat} (h : a ≤ b) :
    (2 ^ b : Nat) &&& (2 ^ a - 1) = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)]

private theorem shiftLeft_and_mask_eq_zero (x a : Nat) :
    (x <<< a) &&& (2 ^ a - 1) = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.mul_mod_left]

private theorem shiftRight_shiftLeft (x n : Nat) : (x <<< n) >>> n = x := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos n)]

private theorem shiftRight_eq_zero_of_lt {x n : Nat} (h : x < 2 ^ n) : x >>> n = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

private theorem and_mask_lt (x : Nat) : x &&& (2 ^ 693 - 1) < 2 ^ 693 :=
  Nat.and_lt_two_pow x (Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num))

private theorem or_shiftLeft_and_mask (A B : Nat) :
    (A ||| B <<< 693) &&& (2 ^ 693 - 1) = A &&& (2 ^ 693 - 1) := by
  rw [Nat.and_or_distrib_right, shiftLeft_and_mask_eq_zero, Nat.or_zero]

private theorem or_shiftLeft_shiftRight {A B : Nat} (hA : A < 2 ^ 693) :
    (A ||| B <<< 693) >>> 693 = B := by
  rw [Nat.shiftRight_or_distrib, shiftRight_eq_zero_of_lt hA, shiftRight_shiftLeft,
    Nat.zero_or]

private theorem shiftRight_lt_mask {E : Nat} (hE : E < 2 ^ 1386) : E >>> 693 < 2 ^ 693 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h : E < 2 ^ 693 * 2 ^ 693 := by
    rw [← Nat.pow_add]; simpa using hE
  exact Nat.div_lt_of_lt_mul h

private def passInv (C : HCtx) (I X : Nat) (n S : Nat) : Prop :=
  S < 2 ^ 1388 ∧
    S.testBit 1386 =
      (openP C (fl I) (fl X) n).any (fun x => (cands C x (fl I) (fl X)).isEmpty) ∧
    S.testBit 1387 = !(forcedP C (fl I) (fl X) n).isEmpty ∧
    fl (S &&& (2 ^ 693 - 1)) = extI C (forcedP C (fl I) (fl X) n) (fl I) ∧
    fl ((S >>> 693) &&& (2 ^ 693 - 1)) = extX C (forcedP C (fl I) (fl X) n) (fl X)

private noncomputable def passStep (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat)
    (n acc : Nat) : Nat :=
  letN acc fun acc =>
    Bool.rec (motive := fun _ => Nat) acc
      (letN (candK LI NL n I X) fun C =>
        Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) acc
            (Nat.lor (Nat.shiftLeft 1 1387) (extK LB NL n (bitPosK C) acc))
            (Nat.beq (Nat.land C (Nat.sub C 1)) 0))
          (Nat.lor acc (Nat.shiftLeft 1 1386)) (Nat.beq C 0))
      (openB PB n I X)

private theorem passK_eq (I X : Nat) :
    passK PB LB LI NL I X =
      Nat.rec (motive := fun _ => Nat) (Nat.lor I (Nat.shiftLeft X 693))
        (passStep PB LB LI NL I X) 693 := by
  unfold passK passStep openB
  simp only [letN_eq]

private theorem passStep_closed {I X n S : Nat} (hob : openB PB n I X = false) :
    passStep PB LB LI NL I X n S = S := by
  simp only [passStep, letN_eq, hob]

private theorem passStep_zero {I X n S : Nat} (hob : openB PB n I X = true)
    (h0 : Nat.beq (candK LI NL n I X) 0 = true) :
    passStep PB LB LI NL I X n S = S ||| 2 ^ 1386 := by
  simp only [passStep, letN_eq, hob, h0, Nat.lor_eq, shiftLeft_one_eq]

private theorem passStep_forced {I X n S : Nat} (hob : openB PB n I X = true)
    (h0 : Nat.beq (candK LI NL n I X) 0 = false)
    (h1 : Nat.beq (Nat.land (candK LI NL n I X) (Nat.sub (candK LI NL n I X) 1)) 0 = true) :
    passStep PB LB LI NL I X n S =
      2 ^ 1387 ||| extK LB NL n (bitPosK (candK LI NL n I X)) S := by
  simp only [passStep, letN_eq, hob, h0, h1, Nat.lor_eq, shiftLeft_one_eq]

private theorem passStep_other {I X n S : Nat} (hob : openB PB n I X = true)
    (h0 : Nat.beq (candK LI NL n I X) 0 = false)
    (h1 : Nat.beq (Nat.land (candK LI NL n I X) (Nat.sub (candK LI NL n I X) 1)) 0 = false) :
    passStep PB LB LI NL I X n S = S := by
  simp only [passStep, letN_eq, hob, h0, h1]

set_option maxRecDepth 4000 in
private theorem passInv_zero (hC : SearchCtx C PB LB LI GI PL NL) {I X : Nat}
    (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) :
    passInv C I X 0 (I ||| X <<< 693) := by
  have hI1386 : I < 2 ^ 1386 :=
    lt_of_lt_of_le hI (Nat.pow_le_pow_right (by norm_num) (by norm_num : 693 ≤ 1386))
  have hI1387 : I < 2 ^ 1387 :=
    lt_of_lt_of_le hI (Nat.pow_le_pow_right (by norm_num) (by norm_num : 693 ≤ 1387))
  have hshift : X <<< 693 < 2 ^ 1386 := by
    rw [Nat.shiftLeft_eq, show (1386 : Nat) = 693 + 693 by norm_num, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hX (Nat.two_pow_pos 693)
  have hshift7 : X <<< 693 < 2 ^ 1387 :=
    lt_of_lt_of_le hshift (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1386 ≤ 1387))
  have hor : I ||| X <<< 693 < 2 ^ 1386 := Nat.or_lt_two_pow hI1386 hshift
  have hlow : (I ||| X <<< 693) &&& (2 ^ 693 - 1) = I := by
    rw [Nat.and_or_distrib_right, Nat.and_two_pow_sub_one_of_lt_two_pow hI,
      shiftLeft_and_mask_eq_zero, Nat.or_zero]
  have hhigh : ((I ||| X <<< 693) >>> 693) &&& (2 ^ 693 - 1) = X := by
    rw [Nat.shiftRight_or_distrib, shiftRight_eq_zero_of_lt hI, shiftRight_shiftLeft,
      Nat.zero_or, Nat.and_two_pow_sub_one_of_lt_two_pow hX]
  unfold passInv
  refine ⟨lt_of_lt_of_le hor (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1386 ≤ 1388)),
    ?_, ?_, ?_, ?_⟩
  · rw [Nat.testBit_or, Nat.testBit_lt_two_pow hI1386, Nat.testBit_lt_two_pow hshift,
      Bool.false_or]
    rfl
  · rw [Nat.testBit_or, Nat.testBit_lt_two_pow hI1387, Nat.testBit_lt_two_pow hshift7,
      Bool.false_or]
    rfl
  · rw [hlow]; rfl
  · rw [hhigh]; rfl

private theorem forcedOf_eq_nil_of_not_singleton {l : List Nat} (h : ∀ j, l ≠ [j]) (n : Nat) :
    forcedOf [(n, l)] = [] := by
  rw [forcedOf_pair]
  cases l with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => exact absurd rfl (h a)
    | cons b t => rfl

private theorem extK_zero_lt (hC : SearchCtx C PB LB LI GI PL NL) {x j : Nat}
    (hx : x < 693) (hj : j < 1024) :
    extK LB NL x j 0 < 2 ^ 1386 := by
  have h := (extK_spec hC hx hj (by norm_num : (0 : Nat) < 2 ^ 693)
    (by norm_num : (0 : Nat) < 2 ^ 693)).1
  simpa using h

private theorem extK_low_eq (LB : Nat → Nat) (NL : Nat → List Nat) (n j S : Nat) :
    (extK LB NL n j S) &&& (2 ^ 693 - 1) =
      (S &&& (2 ^ 693 - 1)) ||| ((extK LB NL n j 0) &&& (2 ^ 693 - 1)) := by
  rw [extK_or, Nat.and_or_distrib_right]

private theorem extK_high_eq (LB : Nat → Nat) (NL : Nat → List Nat) (n j S : Nat) :
    ((extK LB NL n j S) >>> 693) &&& (2 ^ 693 - 1) =
      ((S >>> 693) &&& (2 ^ 693 - 1)) ||| (((extK LB NL n j 0) >>> 693) &&& (2 ^ 693 - 1)) := by
  rw [extK_or, Nat.shiftRight_or_distrib, Nat.and_or_distrib_right]

private theorem extK_step_low (hC : SearchCtx C PB LB LI GI PL NL) {n j S : Nat}
    (hn : n < 693) (hj : j < 1024) :
    fl ((extK LB NL n j S) &&& (2 ^ 693 - 1)) =
      extI C [(n, j)] (fl (S &&& (2 ^ 693 - 1))) := by
  have hspec := extK_spec hC hn hj (and_mask_lt S) (and_mask_lt (S >>> 693))
  have hnum : (S &&& (2 ^ 693 - 1)) ||| ((extK LB NL n j 0) &&& (2 ^ 693 - 1)) =
      extK LB NL n j
        ((S &&& (2 ^ 693 - 1)) ||| ((S >>> 693) &&& (2 ^ 693 - 1)) <<< 693) &&&
        (2 ^ 693 - 1) := by
    conv_rhs => rw [extK_low_eq]
    rw [or_shiftLeft_and_mask, Nat.and_two_pow_sub_one_of_lt_two_pow (and_mask_lt S)]
  rw [extK_low_eq, hnum, hspec.2.1]

private theorem extK_step_high (hC : SearchCtx C PB LB LI GI PL NL) {n j S : Nat}
    (hn : n < 693) (hj : j < 1024) :
    fl (((extK LB NL n j S) >>> 693) &&& (2 ^ 693 - 1)) =
      extX C [(n, j)] (fl ((S >>> 693) &&& (2 ^ 693 - 1))) := by
  have hEKlt : extK LB NL n j 0 < 2 ^ 1386 := extK_zero_lt hC hn hj
  have hEKshift : (extK LB NL n j 0) >>> 693 < 2 ^ 693 := shiftRight_lt_mask hEKlt
  have hspec := extK_spec hC hn hj (and_mask_lt S) (and_mask_lt (S >>> 693))
  have hnum : ((S >>> 693) &&& (2 ^ 693 - 1)) |||
      (((extK LB NL n j 0) >>> 693) &&& (2 ^ 693 - 1)) =
      extK LB NL n j
        ((S &&& (2 ^ 693 - 1)) ||| ((S >>> 693) &&& (2 ^ 693 - 1)) <<< 693) >>> 693 := by
    conv_lhs => rw [Nat.and_two_pow_sub_one_of_lt_two_pow hEKshift]
    conv_rhs => rw [extK_or, Nat.shiftRight_or_distrib, Nat.shiftRight_or_distrib]
    rw [shiftRight_eq_zero_of_lt (and_mask_lt S), shiftRight_shiftLeft, Nat.zero_or]
  rw [extK_high_eq, hnum, hspec.2.2]

private theorem passInv_succ (hC : SearchCtx C PB LB LI GI PL NL) {I X S : Nat}
    (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) (hIX : I &&& X = 0) {n : Nat} (hn : n < 693)
    (h : passInv C I X n S) :
    passInv C I X (n + 1) (passStep PB LB LI NL I X n S) := by
  obtain ⟨hlt, hb6, hb7, hlow, hhigh⟩ := h
  have hob := openB_eq_openF hC hn hI hX
  cases hb : openB PB n I X
  · have hof : openF C (fl I) (fl X) n = false := by rw [← hob, hb]
    rw [passStep_closed hb]
    have hP : openP C (fl I) (fl X) (n + 1) = openP C (fl I) (fl X) n := by
      rw [openP_succ, hof]; simp
    have hF : forcedP C (fl I) (fl X) (n + 1) = forcedP C (fl I) (fl X) n := by
      rw [forcedP_succ, hof]; simp
    unfold passInv
    exact ⟨hlt, by rw [hP]; exact hb6, by rw [hF]; exact hb7,
      by rw [hF]; exact hlow, by rw [hF]; exact hhigh⟩
  · have hof : openF C (fl I) (fl X) n = true := by rw [← hob, hb]
    have hP : openP C (fl I) (fl X) (n + 1) = openP C (fl I) (fl X) n ++ [n] := by
      rw [openP_succ, hof]; simp
    cases hc0 : Nat.beq (candK LI NL n I X) 0
    ·
      have hCne : candK LI NL n I X ≠ 0 := Nat.ne_of_beq_eq_false hc0
      cases hc1 : Nat.beq (Nat.land (candK LI NL n I X) (Nat.sub (candK LI NL n I X) 1)) 0
      ·
        have hCland : Nat.land (candK LI NL n I X) (Nat.sub (candK LI NL n I X) 1) ≠ 0 :=
          Nat.ne_of_beq_eq_false hc1
        have hclist_ne : cands C n (fl I) (fl X) ≠ [] := by
          intro hnil
          have hz : (cands C n (fl I) (fl X)).isEmpty = true := by rw [hnil]; rfl
          rw [cands_isEmpty_eq hC hn hIX] at hz
          change (Nat.beq (candK LI NL n I X) 0) = true at hz
          exact hCne (Nat.eq_of_beq_eq_true hz)
        have hclist_ns : ∀ j, cands C n (fl I) (fl X) ≠ [j] := by
          intro j hj
          exact hCland ((cands_singleton_iff hC hn hIX).1 ⟨j, hj⟩).2
        have hF : forcedP C (fl I) (fl X) (n + 1) = forcedP C (fl I) (fl X) n := by
          rw [forcedP_succ, hof]
          rw [show forcedOf [(n, cands C n (fl I) (fl X))] = [] from
            forcedOf_eq_nil_of_not_singleton hclist_ns n]
          simp
        rw [passStep_other hb hc0 hc1]
        unfold passInv
        refine ⟨hlt, ?_, ?_, ?_, ?_⟩
        · rw [hP, List.any_append]
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          rw [show (cands C n (fl I) (fl X)).isEmpty = false from (isEmpty_eq_false).2 hclist_ne]
          simp [hb6]
        · rw [hF]; exact hb7
        · rw [hF]; exact hlow
        · rw [hF]; exact hhigh
      ·
        have hCland : Nat.land (candK LI NL n I X) (Nat.sub (candK LI NL n I X) 1) = 0 :=
          Nat.eq_of_beq_eq_true hc1
        obtain ⟨j0, hj0⟩ := (cands_singleton_iff hC hn hIX).2 ⟨hCne, hCland⟩
        have hj0lt : j0 < 1024 := by
          have hmem : j0 ∈ (List.range 1024).filter
              (fun i => (candK LI NL n I X).testBit i) := by
            rw [← cands_eq_filter hC hn hIX, hj0]
            exact List.mem_singleton_self j0
          exact List.mem_range.mp (List.mem_of_mem_filter hmem)
        have hCpow : candK LI NL n I X = 2 ^ j0 :=
          (cands_eq_singleton_val hC hn hIX hj0lt).1 hj0
        have hbitpos : bitPosK (candK LI NL n I X) = j0 := by
          rw [hCpow]; exact bitPosK_two_pow hj0lt
        have hF : forcedP C (fl I) (fl X) (n + 1) =
            forcedP C (fl I) (fl X) n ++ [(n, j0)] := by
          rw [forcedP_succ, hof]
          rw [show forcedOf [(n, cands C n (fl I) (fl X))] = [(n, j0)] from by rw [hj0]; rfl]
          simp
        rw [passStep_forced hb hc0 hc1, hbitpos]
        unfold passInv
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hEKlt : extK LB NL n j0 0 < 2 ^ 1386 := extK_zero_lt hC hn hj0lt
          have hExtKlt : extK LB NL n j0 S < 2 ^ 1388 := by
            rw [extK_or]
            exact Nat.or_lt_two_pow hlt
              (lt_of_lt_of_le hEKlt
                (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1386 ≤ 1388)))
          exact Nat.or_lt_two_pow (by norm_num : (2 : Nat) ^ 1387 < 2 ^ 1388) hExtKlt
        · have hL : (2 ^ 1387 ||| extK LB NL n j0 S).testBit 1386 = S.testBit 1386 := by
            rw [Nat.testBit_or, Nat.testBit_two_pow, extK_or, Nat.testBit_or]
            simp [Nat.testBit_lt_two_pow (extK_zero_lt hC hn hj0lt)]
          rw [hL, hP, List.any_append]
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          rw [show (cands C n (fl I) (fl X)).isEmpty = false from by rw [hj0]; rfl]
          simp [hb6]
        · have hL : (2 ^ 1387 ||| extK LB NL n j0 S).testBit 1387 = true := by
            rw [Nat.testBit_or, Nat.testBit_two_pow]; simp
          rw [hL, hF]; simp
        · have hL : fl ((2 ^ 1387 ||| extK LB NL n j0 S) &&& (2 ^ 693 - 1)) =
              extI C [(n, j0)] (fl (S &&& (2 ^ 693 - 1))) := by
            rw [Nat.and_or_distrib_right, pow_and_mask_eq_zero (by norm_num : 693 ≤ 1387),
              Nat.zero_or, extK_step_low hC hn hj0lt]
          rw [hL, hF, extI_append, ← hlow]
        · have hL : fl (((2 ^ 1387 ||| extK LB NL n j0 S) >>> 693) &&& (2 ^ 693 - 1)) =
              extX C [(n, j0)] (fl ((S >>> 693) &&& (2 ^ 693 - 1))) := by
            rw [Nat.shiftRight_or_distrib]
            rw [show (2 ^ 1387 : Nat) >>> 693 = 2 ^ 694 from by
              rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (by norm_num : 693 ≤ 1387)
                (by norm_num : 0 < 2), show 1387 - 693 = 694 by norm_num]]
            rw [Nat.and_or_distrib_right, pow_and_mask_eq_zero (by norm_num : 693 ≤ 694),
              Nat.zero_or, extK_step_high hC hn hj0lt]
          rw [hL, hF, extX_append, ← hhigh]
    ·
      have hC0 : candK LI NL n I X = 0 := Nat.eq_of_beq_eq_true hc0
      have hclist0 : cands C n (fl I) (fl X) = [] := by
        have hz : (cands C n (fl I) (fl X)).isEmpty = true := by
          rw [cands_isEmpty_eq hC hn hIX]
          change (Nat.beq (candK LI NL n I X) 0) = true
          exact hc0
        exact List.isEmpty_iff.mp hz
      have hF : forcedP C (fl I) (fl X) (n + 1) = forcedP C (fl I) (fl X) n := by
        rw [forcedP_succ, hof]
        rw [show forcedOf [(n, cands C n (fl I) (fl X))] = [] from by rw [hclist0]; rfl]
        simp
      rw [passStep_zero hb hc0]
      unfold passInv
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.or_lt_two_pow hlt (by norm_num : (2 : Nat) ^ 1386 < 2 ^ 1388)
      · have hL : (S ||| 2 ^ 1386).testBit 1386 = true := by
          rw [Nat.testBit_or, Nat.testBit_two_pow]; simp
        rw [hL, hP, List.any_append]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        rw [show (cands C n (fl I) (fl X)).isEmpty = true from by rw [hclist0]; rfl]
        simp
      · have hL : (S ||| 2 ^ 1386).testBit 1387 = S.testBit 1387 := by
          rw [Nat.testBit_or, Nat.testBit_two_pow]; simp
        rw [hL, hF]; exact hb7
      · rw [hF]
        rw [show (S ||| 2 ^ 1386) &&& (2 ^ 693 - 1) = S &&& (2 ^ 693 - 1) from by
          rw [Nat.and_or_distrib_right, pow_and_mask_eq_zero (by norm_num : 693 ≤ 1386),
            Nat.or_zero]]
        exact hlow
      · rw [hF]
        rw [show ((S ||| 2 ^ 1386) >>> 693) &&& (2 ^ 693 - 1) =
            (S >>> 693) &&& (2 ^ 693 - 1) from by
          rw [Nat.shiftRight_or_distrib]
          rw [show (2 ^ 1386 : Nat) >>> 693 = 2 ^ 693 from by
            rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (by norm_num : 693 ≤ 1386)
              (by norm_num : 0 < 2), show 1386 - 693 = 693 by norm_num]]
          rw [Nat.and_or_distrib_right, pow_and_mask_eq_zero (le_refl 693), Nat.or_zero]]
        exact hhigh

theorem passK_spec (hC : SearchCtx C PB LB LI GI PL NL) {I X : Nat} (hI : I < 2 ^ 693)
    (hX : X < 2 ^ 693) (hIX : I &&& X = 0) :
    (passK PB LB LI NL I X).testBit 1386 = (candsAt C (fl I) (fl X)).any (fun c => c.2.isEmpty) ∧
      (passK PB LB LI NL I X).testBit 1387 = !(forcedOf (candsAt C (fl I) (fl X))).isEmpty ∧
      extI C (forcedOf (candsAt C (fl I) (fl X))) (fl I) =
        fl (passK PB LB LI NL I X &&& (2 ^ 693 - 1)) ∧
      extX C (forcedOf (candsAt C (fl I) (fl X))) (fl X) =
        fl ((passK PB LB LI NL I X >>> 693) &&& (2 ^ 693 - 1)) := by
  have hmain : ∀ n ≤ 693, passInv C I X n (Nat.rec (motive := fun _ => Nat)
      (Nat.lor I (Nat.shiftLeft X 693)) (passStep PB LB LI NL I X) n) := by
    intro n
    induction n with
    | zero => intro _; exact passInv_zero hC hI hX
    | succ n ih =>
      intro hn
      exact passInv_succ hC hI hX hIX (by omega) (ih (by omega))
  obtain ⟨-, hb6, hb7, hlow, hhigh⟩ := hmain 693 le_rfl
  rw [passK_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hb6, candsAt_eq_candP, candP, List.any_map]
    rfl
  · rw [hb7, forcedOf_candsAt]
  · rw [hlow, forcedOf_candsAt]
  · rw [hhigh, forcedOf_candsAt]

private theorem pickMin_mem {cs : List (Nat × List Nat)} {d : Nat × List Nat}
    (h : pickMin cs = some d) : d ∈ cs := by
  induction cs with
  | nil => cases h
  | cons c cs ih =>
    unfold pickMin at h
    split at h
    · cases h; exact List.mem_cons_self ..
    · rename_i d' hd'
      split at h
      · cases h; exact List.mem_cons_self ..
      · cases h; exact List.mem_cons_of_mem _ (ih hd')

private theorem pickMin_append (l : List (Nat × List Nat)) (c : Nat × List Nat) :
    pickMin (l ++ [c]) = match pickMin l with
      | none => some c
      | some d => if c.2.length < d.2.length then some c else some d := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.cons_append]
    simp only [pickMin]
    rw [ih]
    cases ht : pickMin t with
    | none =>
      simp only [ht]
      by_cases hac : a.2.length ≤ c.2.length
      · have hca : ¬ c.2.length < a.2.length := by omega
        simp [hac, hca]
      · have hca : c.2.length < a.2.length := by omega
        simp [hac, hca]
    | some d =>
      simp only [ht]
      by_cases had : a.2.length ≤ d.2.length
      · simp only [if_pos had]
        by_cases hcd : c.2.length < d.2.length
        · rw [if_pos hcd]
          by_cases hac : a.2.length ≤ c.2.length
          · have hca : ¬ c.2.length < a.2.length := by omega
            simp [hac, hca]
          · have hca : c.2.length < a.2.length := by omega
            simp [hac, hca]
        · rw [if_neg hcd]
          have hca : ¬ c.2.length < a.2.length := by omega
          simp [had, hca]
      · simp only [if_neg had]
        by_cases hcd : c.2.length < d.2.length
        · have hac : ¬ a.2.length ≤ c.2.length := by omega
          simp [hcd, hac]
        · simp [had, hcd]
private def pickEnc (cs : List (Nat × List Nat)) : Nat :=
  match pickMin cs with
  | none => 1024 * 2048
  | some d => 1024 * d.2.length + d.1

private def minInv (C : HCtx) (I X : Nat) (n S : Nat) : Prop :=
  S = pickEnc (candP C (fl I) (fl X) n)

private noncomputable def minStep (PB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat)
    (n acc : Nat) : Nat :=
  letN acc fun acc =>
    Bool.rec (motive := fun _ => Nat) acc
      (letN (pop1024 (candK LI NL n I X)) fun c =>
        Bool.rec (motive := fun _ => Nat) acc
          (Nat.add (Nat.mul 1024 c) n) (Nat.blt c (Nat.div acc 1024)))
      (openB PB n I X)

private theorem minAccK_eq (I X : Nat) :
    minAccK PB LI NL I X =
      Nat.rec (motive := fun _ => Nat) (Nat.mul 1024 2048) (minStep PB LI NL I X) 693 := by
  unfold minAccK minStep openB
  simp only [letN_eq]

private theorem minInv_zero (C : HCtx) (I X : Nat) : minInv C I X 0 (1024 * 2048) := by
  unfold minInv pickEnc
  rw [show candP C (fl I) (fl X) 0 = [] from rfl]
  rfl

private theorem pickMin_eq_none_iff (cs : List (Nat × List Nat)) :
    pickMin cs = none ↔ cs = [] := by
  cases cs with
  | nil => simp [pickMin]
  | cons c cs =>
    cases hcs : pickMin cs with
    | none => simp [pickMin, hcs]
    | some d => by_cases hc : c.2.length ≤ d.2.length <;> simp [pickMin, hcs, hc]

private theorem mem_candP {I X : Flags} {n : Nat} {e : Nat × List Nat}
    (h : e ∈ candP C I X n) : e.1 < n ∧ e.2 = cands C e.1 I X := by
  change e ∈ (openP C I X n).map (fun x => (x, cands C x I X)) at h
  obtain ⟨x, hx, hxs⟩ := List.mem_map.mp h
  have hxlt : x < n := List.mem_range.mp (List.mem_filter.mp hx).1
  rw [← hxs]
  exact ⟨hxlt, rfl⟩

private theorem div_1024 (a b : Nat) (hb : b < 1024) : (1024 * a + b) / 1024 = a := by
  rw [Nat.mul_add_div (show 0 < 1024 by norm_num), Nat.div_eq_of_lt hb, Nat.add_zero]

private theorem pickEnc_append (l : List (Nat × List Nat)) (c : Nat × List Nat) :
    pickEnc (l ++ [c]) = match pickMin l with
      | none => 1024 * c.2.length + c.1
      | some d => if c.2.length < d.2.length then 1024 * c.2.length + c.1
        else 1024 * d.2.length + d.1 := by
  unfold pickEnc
  rw [pickMin_append]
  cases pickMin l with
  | none => rfl
  | some d => by_cases hcd : c.2.length < d.2.length <;> simp [hcd]

private theorem minStep_closed {I X n S : Nat} (hob : openB PB n I X = false) :
    minStep PB LI NL I X n S = S := by
  unfold minStep
  rw [letN_eq, hob]

private theorem minStep_pos {I X n S : Nat} (hob : openB PB n I X = true)
    (hb : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) = true) :
    minStep PB LI NL I X n S =
      Nat.add (Nat.mul 1024 (pop1024 (candK LI NL n I X))) n := by
  unfold minStep
  rw [letN_eq, hob, letN_eq, hb]

private theorem minStep_neg {I X n S : Nat} (hob : openB PB n I X = true)
    (hb : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) = false) :
    minStep PB LI NL I X n S = S := by
  unfold minStep
  rw [letN_eq, hob, letN_eq, hb]

private theorem minInv_succ (hC : SearchCtx C PB LB LI GI PL NL) {I X S : Nat}
    (hI : I < 2 ^ 693) (hX : X < 2 ^ 693) (hIX : I &&& X = 0) {n : Nat} (hn : n < 693)
    (h : minInv C I X n S) :
    minInv C I X (n + 1) (minStep PB LI NL I X n S) := by
  have hob := openB_eq_openF hC hn hI hX
  unfold minInv at h ⊢
  by_cases ho : openF C (fl I) (fl X) n = true
  · have hob' : openB PB n I X = true := by rw [hob]; exact ho
    have hpc : pop1024 (candK LI NL n I X) = (cands C n (fl I) (fl X)).length := by
      rw [pop1024_eq (candK_spec hC hn hIX).1, cands_eq_filter hC hn hIX]
    have hlen : (cands C n (fl I) (fl X)).length ≤ 1024 := by
      rw [cands_eq_filter hC hn hIX]
      simpa [List.length_range] using List.length_filter_le
        (fun j => (candK LI NL n I X).testBit j) (List.range 1024)
    rw [candP_succ, ho, if_pos rfl, pickEnc_append]
    cases hp : pickMin (candP C (fl I) (fl X) n) with
    | none =>
      have hn0 : candP C (fl I) (fl X) n = [] := (pickMin_eq_none_iff _).1 hp
      have hS : S = 1024 * 2048 := by rw [h, hn0]; rfl
      have hdiv : Nat.div S 1024 = 2048 := by
        rw [hS]
      have hblt : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) = true := by
        rw [Nat.blt_eq]; rw [hpc, hdiv]; omega
      rw [minStep_pos hob' hblt, hpc]
      simp
    | some d =>
      have hdmem : d ∈ candP C (fl I) (fl X) n := pickMin_mem hp
      obtain ⟨hd1, -⟩ := mem_candP hdmem
      have hd1lt : d.1 < 1024 := by omega
      have hS : S = 1024 * d.2.length + d.1 := by
        rw [h]; simp [pickEnc, hp]
      have hdiv : Nat.div S 1024 = d.2.length := by
        rw [hS]; exact div_1024 d.2.length d.1 hd1lt
      by_cases hcd : (cands C n (fl I) (fl X)).length < d.2.length
      · have hblt : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) = true := by
          rw [Nat.blt_eq]; rw [hpc, hdiv]; exact hcd
        rw [minStep_pos hob' hblt, hpc]; simp [hcd]
      · have hblt : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) = false := by
          cases hb : Nat.blt (pop1024 (candK LI NL n I X)) (Nat.div S 1024) with
          | false => rfl
          | true =>
            rw [Nat.blt_eq] at hb
            rw [hpc, hdiv] at hb
            exact absurd hb hcd
        rw [minStep_neg hob' hblt, hS]; simp [hcd]
  · have hof : openF C (fl I) (fl X) n = false := by simpa using ho
    have hob' : openB PB n I X = false := by rw [hob]; exact hof
    rw [minStep_closed hob', candP_succ, hof]
    simpa using h

theorem minAccK_spec (hC : SearchCtx C PB LB LI GI PL NL) {I X : Nat} (hI : I < 2 ^ 693)
    (hX : X < 2 ^ 693) (hIX : I &&& X = 0) :
    (pickMin (candsAt C (fl I) (fl X)) = none → minAccK PB LI NL I X = 1024 * 2048) ∧
      ∀ d, pickMin (candsAt C (fl I) (fl X)) = some d →
        minAccK PB LI NL I X = 1024 * d.2.length + d.1 ∧ d.1 < 693 ∧
          d.2 = cands C d.1 (fl I) (fl X) := by
  have hmain : ∀ n ≤ 693, minInv C I X n (Nat.rec (motive := fun _ => Nat)
      (Nat.mul 1024 2048) (minStep PB LI NL I X) n) := by
    intro n
    induction n with
    | zero => intro _; exact minInv_zero C I X
    | succ n ih =>
      intro hn
      exact minInv_succ hC hI hX hIX (by omega) (ih (by omega))
  have hacc : minAccK PB LI NL I X = pickEnc (candP C (fl I) (fl X) 693) := by
    rw [minAccK_eq]
    exact hmain 693 le_rfl
  rw [hacc, candsAt_eq_candP] at *
  constructor
  · intro h
    simp only [pickEnc, h]
  · intro d hd
    cases d with
    | mk d1 d2 =>
      have hmem : (d1, d2) ∈ candP C (fl I) (fl X) 693 := pickMin_mem hd
      change (d1, d2) ∈ (openP C (fl I) (fl X) 693).map
        (fun x => (x, cands C x (fl I) (fl X))) at hmem
      obtain ⟨x, hx, hxd⟩ := List.mem_map.mp hmem
      have hx' : x < 693 := List.mem_range.mp (List.mem_filter.mp hx).1
      injection hxd with hd1 hd2
      have hp : pickEnc (candP C (fl I) (fl X) 693) = 1024 * d2.length + d1 := by
        unfold pickEnc
        rw [hd]
      rw [hp]
      exact ⟨rfl, by rw [← hd1]; exact hx', by rw [← hd2, hd1]⟩

end CFSG.KC.Misc.Hyp

end
