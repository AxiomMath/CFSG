module

public import Certificates.Data.Kernel.Fi22.LHK
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.Fi22LH

open CFSG.KC.Enum CFSG.KS

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem notB_eq (b : Bool) : notB b = !b := by
  cases b <;> rfl

theorem bEq_eq (a b : Bool) : bEq a b = (a == b) := by
  cases a <;> cases b <;> rfl

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.2 fun e => h (by rw [Nat.blt_eq] at e; exact e)

theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [Nat.beq_eq]
  exact h

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (by rw [Nat.beq_eq] at e; exact e)

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  Raw.Orb.allN_iff

theorem foldN_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s :=
  Raw.Orb.foldN_eq n f s

theorem foldUp_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp n f s = (List.range n).foldl (fun s i => f i s) s :=
  Raw.Orb.foldUp_eq n f s

theorem sumBelow_eq (m hi : Nat) (f : Nat → Nat) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : Nat → Nat) (k : Nat),
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : Nat), Bool.rec (motive := fun _ => Nat) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, CFSG.KC.Loop.sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + CFSG.KC.Loop.sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl]
        omega
      simp only [e, sel, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem sum351_eq (f : Nat → Nat) : sum351 f = ∑ j ∈ Finset.range 351, f j :=
  sumBelow_eq 351 6 f (by norm_num)

theorem fld_eq (q o w : Nat) : fld(q, o, 2 ^ w - 1) = q / 2 ^ o % 2 ^ w := by
  change (q >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fd_eq (q o w : Nat) : fd q o (2 ^ w - 1) = q / 2 ^ o % 2 ^ w := fld_eq q o w

theorem fd_le (q o m : Nat) : fd q o m ≤ m := Nat.and_le_right

theorem ent_eq (r x : Nat) : ent r x = r / 2 ^ (12 * x) % 2 ^ 12 := fld_eq r (12 * x) 12

theorem ent_lt (r x : Nat) : ent r x < 4096 := by
  rw [ent_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem e14_eq (r x : Nat) : e14 r x = r / 2 ^ (14 * x) % 2 ^ 14 := fld_eq r (14 * x) 14

theorem e14_lt (r x : Nat) : e14 r x < 16384 := by
  rw [e14_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem testBit_fld (q o w i : Nat) :
    (fld(q, o, 2 ^ w - 1)).testBit i = (decide (i < w) && q.testBit (o + i)) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem m3510_eq : m3510 = 2 ^ 3510 - 1 := by
  change (1 <<< 3510) - 1 = _
  rw [Nat.one_shiftLeft]

theorem sb_eq (q : Nat) : sb q = q / 2 ^ 4212 % 2 ^ 3510 := by
  unfold sb
  rw [m3510_eq, fld_eq]

theorem sb_lt (q : Nat) : sb q < 2 ^ 3510 := by
  rw [sb_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem testBit_sb (q y : Nat) : (sb q).testBit y = (decide (y < 3510) && q.testBit (4212 + y)) := by
  unfold sb
  rw [m3510_eq, testBit_fld]

theorem memB_eq (s y : Nat) : memB s y = s.testBit y := Raw.Orb.hasBit_eq s y

theorem shiftLeft_one (y : Nat) : Nat.shiftLeft (nat_lit 1) y = 2 ^ y := Nat.one_shiftLeft y

theorem testBit_bsF (n : Nat) (f : Nat → Nat) : ∀ d lo y, (bsF n f d lo).testBit y = true ↔
    ∃ i, lo ≤ i ∧ i < lo + 2 ^ d ∧ i < n ∧ f i = y
  | 0, lo, y => by
    change (nIf(Nat.blt lo n, Nat.shiftLeft (nat_lit 1) (f lo), nat_lit 0)).testBit y = true ↔ _
    by_cases h : lo < n
    · rw [blt_true h]
      change (Nat.shiftLeft 1 (f lo)).testBit y = true ↔ _
      rw [shiftLeft_one, Nat.testBit_two_pow]
      constructor
      · intro e
        exact ⟨lo, le_refl _, by simp, h, of_decide_eq_true e⟩
      · rintro ⟨i, h1, h2, -, h4⟩
        have : i = lo := by simp at h2; omega
        subst this
        exact decide_eq_true h4
    · rw [blt_false h]
      change (0 : Nat).testBit y = true ↔ _
      rw [Nat.zero_testBit]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro i h1 h2 h3
      simp at h2
      omega
  | d + 1, lo, y => by
    change (Nat.lor (bsF n f d lo) (bsF n f d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))).testBit y
      = true ↔ _
    rw [show Nat.lor (bsF n f d lo) (bsF n f d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) =
      bsF n f d lo ||| bsF n f d (lo + 2 ^ d) by rw [shiftLeft_one]; rfl, Nat.testBit_or,
      Bool.or_eq_true, testBit_bsF n f d lo y, testBit_bsF n f d (lo + 2 ^ d) y]
    constructor
    · rintro (⟨i, h1, h2, h3, h4⟩ | ⟨i, h1, h2, h3, h4⟩)
      · exact ⟨i, h1, by rw [Nat.pow_succ]; omega, h3, h4⟩
      · exact ⟨i, by omega, by rw [Nat.pow_succ]; omega, h3, h4⟩
    · rintro ⟨i, h1, h2, h3, h4⟩
      rcases Nat.lt_or_ge i (lo + 2 ^ d) with h | h
      · exact Or.inl ⟨i, h1, h, h3, h4⟩
      · exact Or.inr ⟨i, h, by rw [Nat.pow_succ] at h2; omega, h3, h4⟩

theorem testBit_bsP (n : Nat) (p : Nat → Bool) : ∀ d lo y, (bsP n p d lo).testBit y = true ↔
    lo ≤ y ∧ y < lo + 2 ^ d ∧ y < n ∧ p y = true
  | 0, lo, y => by
    change (nIf(Nat.blt lo n, nIf(p lo, Nat.shiftLeft (nat_lit 1) lo, nat_lit 0), nat_lit 0)).testBit y
      = true ↔ _
    by_cases h : lo < n
    · rw [blt_true h]
      change (nIf(p lo, Nat.shiftLeft (nat_lit 1) lo, nat_lit 0)).testBit y = true ↔ _
      rw [nIf_eq]
      by_cases hp : p lo = true
      · rw [if_pos hp, shiftLeft_one, Nat.testBit_two_pow]
        constructor
        · intro e
          have := of_decide_eq_true e
          subst this
          exact ⟨le_refl _, by simp, h, hp⟩
        · rintro ⟨h1, h2, -, -⟩
          simp at h2
          exact decide_eq_true (by omega)
      · rw [if_neg hp, Nat.zero_testBit]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro h1 h2 _ hy
        simp at h2
        have : y = lo := by omega
        subst this
        exact hp hy
    · rw [blt_false h]
      change (0 : Nat).testBit y = true ↔ _
      rw [Nat.zero_testBit]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro h1 h2 h3
      simp at h2
      omega
  | d + 1, lo, y => by
    change (Nat.lor (bsP n p d lo) (bsP n p d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d)))).testBit y
      = true ↔ _
    rw [show Nat.lor (bsP n p d lo) (bsP n p d (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) =
      bsP n p d lo ||| bsP n p d (lo + 2 ^ d) by rw [shiftLeft_one]; rfl, Nat.testBit_or,
      Bool.or_eq_true, testBit_bsP n p d lo y, testBit_bsP n p d (lo + 2 ^ d) y, Nat.pow_succ]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, by omega, h3, h4⟩
      · exact ⟨by omega, by omega, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rcases Nat.lt_or_ge y (lo + 2 ^ d) with h | h
      · exact Or.inl ⟨h1, h, h3, h4⟩
      · exact Or.inr ⟨h, by omega, h3, h4⟩

theorem testBit_bsP_zero {n d : Nat} (hn : n ≤ 2 ^ d) (p : Nat → Bool) (y : Nat) :
    (bsP n p d 0).testBit y = (decide (y < n) && p y) := by
  have h := testBit_bsP n p d 0 y
  cases e : (bsP n p d 0).testBit y
  · symm
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_true]
    by_contra hc
    push Not at hc
    have := h.2 ⟨Nat.zero_le _, by omega, hc.1, by simpa using hc.2⟩
    rw [e] at this
    exact Bool.false_ne_true this
  · obtain ⟨-, -, h3, h4⟩ := h.1 e
    simp [h3, h4]

theorem testBit_bsF_zero {n d : Nat} (hn : n ≤ 2 ^ d) (f : Nat → Nat) (y : Nat) :
    (bsF n f d 0).testBit y = true ↔ ∃ i < n, f i = y := by
  rw [testBit_bsF]
  constructor
  · rintro ⟨i, -, -, h3, h4⟩
    exact ⟨i, h3, h4⟩
  · rintro ⟨i, h3, h4⟩
    exact ⟨i, Nat.zero_le _, by omega, h3, h4⟩

theorem testBit_bs (q y : Nat) : (bs q).testBit y = true ↔ ∃ j < 351, ent q j = y :=
  testBit_bsF_zero (by norm_num) _ y

theorem bsF_lt {n d : Nat} (hn : n ≤ 2 ^ d) {f : Nat → Nat} {N : Nat} (hf : ∀ i < n, f i < N) :
    bsF n f d 0 < 2 ^ N := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases e : (bsF n f d 0).testBit i
  · rfl
  · obtain ⟨j, hj, e2⟩ := (testBit_bsF_zero hn f i).1 e
    have := hf j hj
    omega

theorem bsP_lt {n d : Nat} (hn : n ≤ 2 ^ d) (p : Nat → Bool) : bsP n p d 0 < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_bsP_zero hn]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

end CFSG.KS.Fi22LH
