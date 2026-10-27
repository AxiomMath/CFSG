module

public import Certificates.Data.Kernel.E8TenTwoBits
import CFSG.Certificates.Kernel.BenesSound
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenNat
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.E8TenTwoBits

open CFSG.KC CFSG.KC.MonsterConv.Perm E8TenTwo
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

theorem xorN (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem landN (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem lorN (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem shrN (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem shlOne (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : Loop.strictN y k = k y := by
  cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem beq_eq_true {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by subst h; exact Nat.beq_refl a⟩

theorem land_one_eq (s : Nat) : s &&& 1 = if s.testBit 0 = true then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp [h]

theorem beq_land_one (s : Nat) : Nat.beq (Nat.land s 1) 1 = s.testBit 0 := by
  rw [landN, land_one_eq]
  cases s.testBit 0 <;> rfl

theorem beq_bit (x b : Nat) : Nat.beq (Nat.land (Nat.shiftRight x b) 1) 1 = x.testBit b := by
  rw [beq_land_one, shrN, Nat.testBit_shiftRight, Nat.add_zero]

theorem ones_testBit (W q : Nat) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

theorem xor4 (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem ite_bxor (p q : Bool) (b : Nat) :
    (if (p ^^ q) = true then b else 0) = (if p = true then b else 0) ^^^ (if q = true then b else 0) := by
  cases p <;> cases q <;> simp

theorem ite_xor (p q : Bool) (b X Y : Nat) :
    (if (p ^^ q) = true then b else 0) ^^^ (X ^^^ Y) =
      ((if p = true then b else 0) ^^^ X) ^^^ ((if q = true then b else 0) ^^^ Y) := by
  rw [ite_bxor, xor4]

theorem comb_nil (s : Nat) : comb [] s = 0 := rfl

theorem comb_cons (b : Nat) (B : List Nat) (s : Nat) :
    comb (b :: B) s = (if s.testBit 0 = true then b else 0) ^^^ comb B (s >>> 1) := by
  change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 b (Nat.beq (Nat.land s 1) 1))
    (comb B (Nat.shiftRight s 1)) = _
  rw [nIf_eq, beq_land_one]
  rfl

theorem comb_xor (B : List Nat) : ∀ s t, comb B (s ^^^ t) = comb B s ^^^ comb B t := by
  induction B with
  | nil => intro s t; rw [comb_nil, comb_nil, comb_nil]; rfl
  | cons b B ih =>
    intro s t
    rw [comb_cons, comb_cons, comb_cons, Nat.shiftRight_xor_distrib, ih, Nat.testBit_xor, ite_xor]

theorem comb_zero (B : List Nat) : comb B 0 = 0 := by
  have h := comb_xor B 0 0
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem comb_code (b : Nat) (B : List Nat) (p : Bool) (c : Nat) :
    comb (b :: B) ((if p = true then 1 else 0) + 2 * c) = (if p = true then b else 0) ^^^ comb B c := by
  rw [comb_cons]
  have h0 : ((if p = true then 1 else 0) + 2 * c).testBit 0 = p := by
    rw [Nat.testBit_zero]
    cases p <;> simp
  have h1 : ((if p = true then 1 else 0) + 2 * c) >>> 1 = c := by
    rw [Nat.shiftRight_eq_div_pow, pow_one]
    cases p
    · simp
    · simp only [if_true]
      omega
  rw [h0, h1]

def codeL : List Nat → Nat → Nat
  | [], _ => 0
  | L :: Ls, m => (if L.testBit m = true then 2 ^ Ls.length else 0) + codeL Ls m

def parB (f m : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => parB f m n ^^ (f.testBit n && m.testBit n)

def cP : List Nat → Nat → Nat
  | [], _ => 0
  | f :: F, m => (if parB f m 20 = true then 1 else 0) + 2 * cP F m

theorem codeL_lt (Ls : List Nat) (m : Nat) : codeL Ls m < 2 ^ Ls.length := by
  induction Ls with
  | nil => simp [codeL]
  | cons L Ls ih =>
    simp only [codeL, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem cP_lt (F : List Nat) (m : Nat) : cP F m < 2 ^ F.length := by
  induction F with
  | nil => simp [cP]
  | cons f F ih =>
    simp only [cP, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem codeL_append (l₁ l₂ : List Nat) (m : Nat) :
    codeL (l₁ ++ l₂) m = codeL l₁ m * 2 ^ l₂.length + codeL l₂ m := by
  induction l₁ with
  | nil => simp [codeL]
  | cons L l ih =>
    simp only [List.cons_append, codeL, ih, List.length_append, pow_add]
    split_ifs <;> ring

theorem parB_xor (f x y : Nat) (n : Nat) : parB f (x ^^^ y) n = (parB f x n ^^ parB f y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parB, Nat.testBit_xor, ih]
    cases parB f x n <;> cases parB f y n <;> cases f.testBit n <;> cases x.testBit n <;>
      cases y.testBit n <;> rfl

theorem parB_pow (f j n : Nat) : parB f (2 ^ j) n = (decide (j < n) && f.testBit j) := by
  induction n with
  | zero => simp [parB]
  | succ n ih =>
    rw [parB, ih, Nat.testBit_two_pow]
    by_cases h : j = n
    · subst h
      simp
    · have h1 : (j < n + 1) ↔ j < n := by omega
      simp [h, h1]

theorem flaneRec_testBit (k F m : Nat) (hm : m < 2 ^ k) : ∀ n, n ≤ k →
    (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor acc (idPlane (2 ^ k) b)) (Nat.beq (Nat.land (Nat.shiftRight F b) 1) 1))
      n : Nat).testBit m = parB F m n := by
  intro n
  induction n with
  | zero =>
    intro _
    exact Nat.zero_testBit m
  | succ n ih =>
    intro hn
    change (Bool.rec (motive := fun _ => Nat) _ _ _).testBit m = _
    rw [nIf_eq, beq_bit, xorN, parB]
    split_ifs with hF
    · rw [Nat.testBit_xor, ih (by omega), Benes.idPlane_testBit (by omega), hF, decide_eq_true hm]
    · rw [ih (by omega)]
      simp [hF]

theorem flane_testBit {F m : Nat} (hm : m < 2 ^ 20) : (flane 20 F).testBit m = parB F m 20 :=
  flaneRec_testBit 20 F m hm 20 le_rfl

theorem codeL_lanes (F : List Nat) {m : Nat} (hm : m < 2 ^ 20) : codeL (lanes 20 F) m = cP F m := by
  unfold lanes
  induction F with
  | nil => rfl
  | cons f F ih =>
    rw [List.map_cons, List.reverse_cons, codeL_append, ih]
    simp only [codeL, List.length_cons, List.length_nil, pow_zero, pow_one, Nat.zero_add,
      flane_testBit hm, cP]
    split_ifs <;> omega

theorem cP_comb_xor (F : List Nat) : ∀ (B : List Nat) (x y : Nat),
    comb B (cP F (x ^^^ y)) = comb B (cP F x) ^^^ comb B (cP F y) := by
  induction F with
  | nil => intro B x y; simp only [cP, comb_zero, Nat.xor_self]
  | cons f F ih =>
    intro B x y
    cases B with
    | nil => rw [comb_nil, comb_nil, comb_nil]; rfl
    | cons b B =>
      simp only [cP]
      rw [comb_code, comb_code, comb_code, parB_xor, ih, ite_xor]

theorem cP_pow (F : List Nat) {j : Nat} (hj : j < 20) : cP F (2 ^ j) = colCode F j := by
  induction F with
  | nil => rfl
  | cons f F ih =>
    have e : colCode (f :: F) j = (f >>> j &&& 1) + 2 * colCode F j := rfl
    rw [cP, e, ih, parB_pow, land_one_eq, Nat.testBit_shiftRight, Nat.add_zero, decide_eq_true hj,
      Bool.true_and]

theorem evalT_cons (O L : Nat) (Ls : List Nat) (T acc : Nat) :
    evalT O (L :: Ls) T acc = if T = 0 then 0 else
      evalT O Ls (T % 2 ^ 2 ^ Ls.length) (acc &&& (O ^^^ L)) |||
        evalT O Ls (T / 2 ^ 2 ^ Ls.length) (acc &&& L) := by
  change Bool.rec (motive := fun _ => Nat)
      (Nat.lor (Loop.strictN (Nat.land acc (Nat.xor O L))
          (fun a => evalT O Ls (Nat.mod T (Nat.shiftLeft 1 (Nat.shiftLeft 1 Ls.length))) a))
        (Loop.strictN (Nat.land acc L)
          (fun a => evalT O Ls (Nat.div T (Nat.shiftLeft 1 (Nat.shiftLeft 1 Ls.length))) a)))
      0 (Nat.beq T 0) = _
  rw [nIf_eq, strictN_eq, strictN_eq, shlOne, shlOne]
  by_cases h : T = 0
  · rw [if_pos (beq_eq_true.2 h), if_pos h]
  · rw [if_neg (fun h' => h (beq_eq_true.1 h')), if_neg h]
    rfl

theorem evalT_sound {O m : Nat} (hO : O.testBit m = true) : ∀ (Ls : List Nat) (T acc : Nat),
    (evalT O Ls T acc).testBit m = true → acc.testBit m = true ∧ T.testBit (codeL Ls m) = true := by
  intro Ls
  induction Ls with
  | nil =>
    intro T acc h
    have e : evalT O [] T acc = if T.testBit 0 = true then acc else 0 := by
      change Bool.rec (motive := fun _ => Nat) 0 acc (Nat.beq (Nat.land T 1) 1) = _
      rw [nIf_eq, beq_land_one]
    rw [e] at h
    split_ifs at h with hT
    · exact ⟨h, hT⟩
    · simp at h
  | cons L Ls ih =>
    intro T acc h
    rw [evalT_cons] at h
    split_ifs at h with hT0
    · simp at h
    · rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := ih _ _ h
        rw [Nat.testBit_and, Nat.testBit_xor, hO, Bool.and_eq_true] at h1
        have hL : L.testBit m = false := by simpa using h1.2
        refine ⟨h1.1, ?_⟩
        rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at h2
        simpa [codeL, hL] using h2.2
      · obtain ⟨h1, h2⟩ := ih _ _ h
        rw [Nat.testBit_and, Bool.and_eq_true] at h1
        refine ⟨h1.1, ?_⟩
        rw [Nat.testBit_div_two_pow] at h2
        have e : codeL (L :: Ls) m = codeL Ls m + 2 ^ Ls.length := by
          rw [codeL, if_pos h1.2, Nat.add_comm]
        rw [e]
        exact h2

theorem cover_cons (k : Nat) (d : List Nat × List Nat × Nat) (D : List (List Nat × List Nat × Nat)) :
    cover k (d :: D) = evalT (ones (2 ^ k)) (lanes k d.1) d.2.2 (ones (2 ^ k)) ||| cover k D := by
  change Loop.strictN (evalT (ones (Nat.shiftLeft 1 k)) (lanes k d.1) d.2.2 (ones (Nat.shiftLeft 1 k)))
    (fun c => Nat.lor c (cover k D)) = _
  rw [strictN_eq, shlOne]
  rfl

theorem cover_sound (k m : Nat) : ∀ D : List (List Nat × List Nat × Nat), (cover k D).testBit m = true →
    ∃ d ∈ D, (evalT (ones (2 ^ k)) (lanes k d.1) d.2.2 (ones (2 ^ k))).testBit m = true := by
  intro D
  induction D with
  | nil =>
    intro h
    have e : cover k [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    cases h
  | cons d D ih =>
    intro h
    rw [cover_cons, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨d, List.mem_cons_self, h⟩
    · obtain ⟨d', hd', h'⟩ := ih h
      exact ⟨d', List.mem_cons_of_mem _ hd', h'⟩

theorem coverOK_sound {D : List (List Nat × List Nat × Nat)} (h : coverOK 20 D = true) {m : Nat}
    (h1 : 0 < m) (h2 : m < 2 ^ 20) : ∃ d ∈ D, d.2.2.testBit (codeL (lanes 20 d.1) m) = true := by
  have hc := beq_eq_true.1 (h : Nat.beq (cover 20 D) (Nat.xor (ones (Nat.shiftLeft 1 20)) 1) = true)
  have hone : (1 : Nat).testBit m = false := by
    have e : (1 : Nat) = 2 ^ 0 := rfl
    rw [e, Nat.testBit_two_pow, decide_eq_false_iff_not]
    omega
  have hO : (ones (2 ^ 20)).testBit m = true := by
    rw [ones_testBit, decide_eq_true h2]
  have hm : (cover 20 D).testBit m = true := by
    rw [hc, xorN, shlOne, Nat.testBit_xor, hO, hone]
    rfl
  obtain ⟨d, hd, he⟩ := cover_sound 20 m D hm
  exact ⟨d, hd, (evalT_sound hO _ _ _ he).2⟩

theorem codesOK_eq (D : List (List Nat × List Nat × Nat)) : codesOK D = codesIn oBits D := by
  unfold codesOK
  generalize oBits = n
  cases n <;> rfl

theorem codesIn_sound {O : Nat} {D : List (List Nat × List Nat × Nat)} (h : codesIn O D = true)
    {d : List Nat × List Nat × Nat} (hd : d ∈ D) {s : Nat} (hs : s < 2 ^ d.2.1.length)
    (hT : d.2.2.testBit s = true) : comb d.2.1 s < 2 ^ 20 ∧ O.testBit (comb d.2.1 s) = true := by
  unfold codesIn at h
  rw [List.all_eq_true] at h
  have h2 := h d hd
  simp only [List.all_eq_true, List.mem_range] at h2
  have h3 := h2 s hs
  rw [bIf_eq, beq_bit, if_pos hT, andB_eq, Bool.and_eq_true, beq_bit] at h3
  exact ⟨Nat.le_of_ble_eq_true h3.1, h3.2⟩

theorem colsOK_sound {F B C : List Nat} (h : colsOK F B C = true) :
    ∀ j < 20, C.getD j 0 ^^^ 2 ^ j = comb B (colCode F j) := by
  unfold colsOK at h
  rw [andB_eq, Bool.and_eq_true, beq_eq_true, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro j hj
  have hmem : (C[j]'(by omega), j) ∈ List.zip C (List.range 20) := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp [hlen, hj], by simp⟩
  have := beq_eq_true.1 (hall _ hmem)
  rw [getD_of_lt _ _ (by omega)]
  simpa [xorN, Nat.one_shiftLeft] using this

theorem factOK_sound {G : List (List Nat)} {D : List (List Nat × List Nat × Nat)}
    (h : factOK G D = true) {d : List Nat × List Nat × Nat} (hd : d ∈ D) :
    ∃ w ∈ transWords, d.1.length = d.2.1.length ∧ colsOK d.1 d.2.1 (compCols G w) = true := by
  unfold factOK at h
  rw [andB_eq, Bool.and_eq_true, beq_eq_true, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hd
  have hmem : (transWords[i]'(by omega), D[i]) ∈ List.zip transWords D := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp⟩
  have := hall _ hmem
  simp only [andB_eq, Bool.and_eq_true, beq_eq_true] at this
  exact ⟨_, List.getElem_mem (by omega), this.1, this.2⟩

theorem foldl_bits (l : List (Nat × Nat × Nat)) (a x : Nat)
    (h : (l.foldl (fun a e => Nat.lor a (Nat.shiftLeft 1 e.1)) a).testBit x = true) :
    a.testBit x = true ∨ ∃ e ∈ l, e.1 = x := by
  induction l generalizing a with
  | nil => exact Or.inl h
  | cons e l ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · rw [lorN, shlOne, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨e, List.mem_cons_self, by simpa using h1⟩
    · obtain ⟨e', he', hx⟩ := h1
      exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hx⟩

theorem oBits_sound {x : Nat} (h : oBits.testBit x = true) : ∃ e ∈ bfsTab, e.1 = x := by
  rcases foldl_bits bfsTab 0 x h with h1 | h1
  · simp at h1
  · exact h1

theorem foldl_set_true (l : List (Nat × Nat × Nat)) (A : Array Bool) {d : Nat} (hd : d < A.size)
    (h : A.getD d false = true ∨ ∃ e ∈ l, e.1 = d) :
    (l.foldl (fun a e => a.set! e.1 true) A).getD d false = true := by
  induction l generalizing A with
  | nil =>
    rcases h with h | ⟨e, he, _⟩
    · exact h
    · cases he
  | cons e l ih =>
    rw [List.foldl_cons]
    have hs : (A.set! e.1 true).size = A.size := by simp
    have hget : (A.set! e.1 true).getD d false = if e.1 = d then true else A.getD d false := by
      by_cases he : e.1 = d
      · rw [if_pos he, ← he]
        rw [← he] at hd
        simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, hd]
      · rw [if_neg he]
        simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, he]
    apply ih _ (by rw [hs]; exact hd)
    rcases h with h | ⟨e', he', hed⟩
    · left
      rw [hget]
      by_cases he : e.1 = d
      · rw [if_pos he]
      · rw [if_neg he]
        exact h
    · rcases List.mem_cons.1 he' with rfl | he''
      · left
        rw [hget, if_pos hed]
      · right
        exact ⟨e', he'', hed⟩

theorem oSet_true {d : Nat} (hd : d < 2 ^ 20) (h : ∃ e ∈ bfsTab, e.1 = d) :
    (oSet ()).getD d false = true := by
  unfold oSet
  exact foldl_set_true bfsTab _ (by simpa using hd) (Or.inr h)

theorem allBelow_of (f : Nat → Bool) (n : Nat) (h : ∀ m, 1 ≤ m → m ≤ n → f m = true) :
    E8TenTwo.allBelow f n = true := by
  induction n with
  | zero => simp only [E8TenTwo.allBelow]
  | succ k ih =>
    unfold E8TenTwo.allBelow
    rw [if_pos (h (k + 1) (by omega) le_rfl)]
    exact ih (fun m h1 h2 => h m h1 (by omega))

theorem lin_of_cols {F B C : List Nat} (hC : ∀ j < 20, C.getD j 0 ^^^ 2 ^ j = comb B (colCode F j)) :
    ∀ m, m < 2 ^ 20 → applyCols C m ^^^ m = comb B (cP F m) := by
  refine lin_induct ?_ ?_ ?_
  · have h := cP_comb_xor F B 0 0
    simp only [Nat.xor_self] at h
    rw [h, applyCols_zero]
    rfl
  · intro j hj
    rw [applyCols_pow _ hj, Nat.one_shiftLeft, cP_pow F hj, hC j hj]
  · intro x y hx hy
    rw [applyCols_xor, cP_comb_xor, ← hx, ← hy]
    exact xor4 _ _ _ _

theorem e8TenTwoCheck_of {D : List (List Nat × List Nat × Nat)} (hrat : ratOk () = true)
    (hcols : colsOk () = true) (hwords : wordsOk () = true) (hbfs : bfsOk () = true)
    (hcov : coverOK 20 D = true) (hfac : factOK (gmats ()) D = true) (hcod : codesOK D = true) :
    e8TenTwoCheck () = true := by
  unfold e8TenTwoCheck
  simp only [hrat, hcols, hwords, hbfs, Bool.true_and]
  apply allBelow_of
  intro m hm1 hm2
  have hm : m < 2 ^ 20 := by omega
  obtain ⟨d, hd, hT⟩ := coverOK_sound hcov (by omega) hm
  obtain ⟨w, hw, hlen, hcolsd⟩ := factOK_sound hfac hd
  have hlin := lin_of_cols (colsOK_sound hcolsd) m hm
  rw [codeL_lanes _ hm] at hT
  rw [codesOK_eq] at hcod
  have hs : cP d.1 m < 2 ^ d.2.1.length := by
    rw [← hlen]
    exact cP_lt d.1 m
  obtain ⟨hlt, hbit⟩ := codesIn_sound hcod hd hs hT
  unfold hasTrans
  rw [List.any_eq_true]
  refine ⟨compCols (gmats ()) w, List.mem_map.2 ⟨w, hw, rfl⟩, ?_⟩
  rw [hlin]
  exact oSet_true hlt (oBits_sound hbit)

end CFSG.KC.E8TenTwoBits

end
