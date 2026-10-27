module

public import CFSG.Certificates.Kernel.Perm16Sound
public import Certificates.Data.Kernel.Co1Dce
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.Co1D

open CFSG.KC CFSG.KC.DceS CFSG.KC.Loop CFSG.KS.P16
open scoped Pointwise

theorem andB_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff (a b : Bool) : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem strictN_eq (v : ℕ) (k : ℕ → ℕ) : strictN v k = k v := by
  cases v <;> rfl

theorem brec_eq {α : Sort*} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem allRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n) (f n) =
      true ↔ _
    rw [andB_iff, allRec_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨fun q hq => h q (by omega), h n (by omega)⟩

theorem allRec2_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => andB (f q) acc) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change andB (f n) (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB (f q) acc) n) =
      true ↔ _
    rw [andB_iff, allRec2_iff f n]
    constructor
    · rintro ⟨h2, h1⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨h n (by omega), fun q hq => h q (by omega)⟩

theorem anyRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun q acc => orB acc (f q)) n = true ↔
      ∃ q < n, f q = true
  | 0 => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨q, hq, _⟩ => absurd hq (Nat.not_lt_zero q)⟩
  | n + 1 => by
    change orB (Nat.rec (motive := fun _ => Bool) false (fun q acc => orB acc (f q)) n) (f n) =
      true ↔ _
    rw [orB_iff, anyRec_iff f n]
    constructor
    · rintro (⟨q, hq, h⟩ | h)
      · exact ⟨q, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨q, hq, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · exact Or.inl ⟨q, hq, h⟩
      · exact Or.inr h

theorem hintLoop (F : ℕ → ℕ → Bool) (m sh : ℕ) : ∀ k, k ≤ m → ∀ H,
    Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun k ih H => andB (F (Nat.sub m (Nat.succ k)) H) (ih (Nat.shiftRight H sh))) k H = true →
    ∀ t < k, F (m - k + t) (H >>> (sh * t)) = true
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | k + 1, hk, H, h, t, ht => by
    change andB (F (Nat.sub m (Nat.succ k)) H)
      (Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun k ih H => andB (F (Nat.sub m (Nat.succ k)) H) (ih (Nat.shiftRight H sh))) k
        (Nat.shiftRight H sh)) = true at h
    rw [andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    rcases t with _ | t
    · simpa using h1
    · have := hintLoop F m sh k (by omega) _ h2 t (by omega)
      have e1 : m - k + t = m - (k + 1) + (t + 1) := by omega
      have e2 : Nat.shiftRight H sh >>> (sh * t) = H >>> (sh * (t + 1)) := by
        change H >>> sh >>> (sh * t) = _
        rw [← Nat.shiftRight_add]
        congr 1
        ring
      rw [e1, e2] at this
      exact this

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  intro i him
  have h1 := (allRec2_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) hi).1 h (i / 64) (by omega)
  have h2 := (allRec2_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem bitAt_iff (A d : ℕ) : bitAt A d = true ↔ A.testBit d = true := by
  unfold bitAt
  rw [Nat.blt_eq]
  change 0 < A &&& 1 <<< d ↔ _
  rw [Nat.one_shiftLeft]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h)
    rw [Nat.testBit_and, Nat.testBit_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [hi.2]
    exact hi.1
  · intro h
    have : (A &&& 2 ^ d).testBit d = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow, h]
      simp
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at this

theorem two_pow_eight_mul (k : ℕ) : 2 ^ (8 * k) = 256 ^ k := by
  rw [pow_mul]
  norm_num

theorem wLet_eq (W i : ℕ) : wLet W i = W / 256 ^ i % 256 := by
  change W >>> (8 * i) &&& 255 = _
  have h : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, two_pow_eight_mul]

theorem wLet_lt (W i : ℕ) : wLet W i < 256 := by
  rw [wLet_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem byte_add_high {W B i n : ℕ} (hi : i < n) :
    (W + B * 256 ^ n) / 256 ^ i % 256 = W / 256 ^ i % 256 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have e : B * 256 ^ (i + d + 1) = 256 ^ i * (256 * (B * 256 ^ d)) := by ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem byte_concat {A B p i : ℕ} (hA : A < 256 ^ p) :
    (A + B * 256 ^ p) / 256 ^ i % 256 =
      if i < p then A / 256 ^ i % 256 else B / 256 ^ (i - p) % 256 := by
  split_ifs with hi
  · exact byte_add_high hi
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + B * 256 ^ p) / 256 ^ (p + j) = B / 256 ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm B,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

theorem land_mask (x k : ℕ) : Nat.land x (Nat.sub (Nat.shiftLeft 1 k) 1) = x % 2 ^ k := by
  change x &&& ((1 <<< k) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem shr_eq (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

theorem lor_shl {a b k : ℕ} (ha : a < 2 ^ k) : Nat.lor a (Nat.shiftLeft b k) = a + b * 2 ^ k := by
  change a ||| b <<< k = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem land_lit (x k m : ℕ) (hm : m = 2 ^ k - 1) : Nat.land x m = x % 2 ^ k := by
  subst hm
  exact Nat.and_two_pow_sub_one_eq_mod x k

theorem testBit_fld16 (x l k : ℕ) :
    (fld16 x l).testBit k = (decide (k < 16) && x.testBit (16 * l + k)) := by
  have e : Nat.shiftLeft l 4 = 16 * l := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    ring
  unfold fld16
  rw [e, Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_shiftRight]
  have e2 : Nat.testBit 65535 k = decide (k < 16) := Nat.testBit_two_pow_sub_one 16 k
  rw [e2, Bool.and_comm]

theorem fld16_lt (x l : ℕ) : fld16 x l < 65536 :=
  Nat.and_lt_two_pow (Nat.shiftRight x (Nat.shiftLeft l 4)) (y := 65535) (n := 16) (by norm_num)

@[expose] def msk (m : ℕ) : Finset (Fin 16) := Finset.univ.filter fun i => m.testBit i.val = true

@[expose] noncomputable def pbBlock (PB l : ℕ) : Finset (Fin 16) :=
  Finset.univ.filter fun p => fl PB p.val = l

@[expose] noncomputable def sysOf (NB OM : ℕ) : Finset (Finset (Fin 16)) :=
  (Finset.range NB).image fun l => msk (fld16 OM l)

@[expose] noncomputable def sysPB (NB PB : ℕ) : Finset (Finset (Fin 16)) :=
  (Finset.range NB).image fun l => pbBlock PB (l + 1)

theorem msk_inj {m m' : ℕ} (hm : m < 2 ^ 16) (hm' : m' < 2 ^ 16) (h : msk m = msk m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 16
  · have := congrArg (fun s => (⟨n, hn⟩ : Fin 16) ∈ s) h
    simp only [msk, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases h1 : m.testBit n <;> cases h2 : m'.testBit n <;> simp_all
  · have h16 : 2 ^ 16 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem msk_nonempty {m : ℕ} (h0 : 0 < m) (hm : m < 2 ^ 16) : (msk m).Nonempty := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h0)
  have hi16 : i < 16 := by
    by_contra hc
    have h16 : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega)] at hi
    exact absurd hi Bool.false_ne_true
  exact ⟨⟨i, hi16⟩, by simp [msk, hi]⟩

theorem testBit_img16 (A B : ℕ → ℕ) (n : ℕ) :
    (Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 0) (nat_lit 4)) (B 0))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 1) (nat_lit 4)) (B 1))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 2) (nat_lit 4)) (B 2))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 3) (nat_lit 4)) (B 3))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 4) (nat_lit 4)) (B 4))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 5) (nat_lit 4)) (B 5))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 6) (nat_lit 4)) (B 6))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 7) (nat_lit 4)) (B 7))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 8) (nat_lit 4)) (B 8))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 9) (nat_lit 4)) (B 9))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 10) (nat_lit 4)) (B 10))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 11) (nat_lit 4)) (B 11))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 12) (nat_lit 4)) (B 12))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 13) (nat_lit 4)) (B 13))) <|
    Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 14) (nat_lit 4)) (B 14)))
      (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A 15) (nat_lit 4)) (B 15)))).testBit n =
      true ↔ ∃ p < 16, A p * 16 + B p = n := by
  have e : ∀ p, Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (A p) (nat_lit 4)) (B p)) =
      2 ^ (A p * 16 + B p) := fun p => by
    change 1 <<< (A p <<< 4 + B p) = _
    rw [Nat.one_shiftLeft, Nat.shiftLeft_eq]
  simp only [e, Nat.lor_eq, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;>
      exact ⟨_, by norm_num, h⟩
  · rintro ⟨p, hp, h⟩
    interval_cases p <;> simp [h]

theorem testBit_imgMasks {P : ℕ} (PB n : ℕ) (hP : P < 2 ^ 64) :
    (imgMasks P PB).testBit n = true ↔ ∃ p < 16, fl PB p * 16 + fl P p = n := by
  have f0 : ∀ x, Nat.land x (nat_lit 15) = fl x 0 := fun x => by
    unfold fl
    rfl
  have hf : ∀ x i, Nat.land (Nat.shiftRight x (4 * i)) 15 = fl x i := fun _ _ => rfl
  unfold imgMasks
  rw [f0 PB, f0 P, hf PB 1, hf P 1, hf PB 2, hf P 2, hf PB 3, hf P 3, hf PB 4, hf P 4, hf PB 5,
    hf P 5, hf PB 6, hf P 6, hf PB 7, hf P 7, hf PB 8, hf P 8, hf PB 9, hf P 9, hf PB 10, hf P 10,
    hf PB 11, hf P 11, hf PB 12, hf P 12, hf PB 13, hf P 13, hf PB 14, hf P 14, hf PB 15, shr60 hP]
  exact testBit_img16 (fl PB) (fl P) n

theorem msk_img {P : ℕ} (hP : IsP P) (PB l : ℕ) :
    msk (fld16 (imgMasks P PB) l) = (perm16 P)⁻¹ • pbBlock PB l := by
  ext i
  rw [Finset.smul_finset_def]
  simp only [msk, pbBlock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Equiv.Perm.smul_def, perm16_inv_apply hP]
  rw [testBit_fld16]
  simp only [i.isLt, decide_true, Bool.true_and]
  rw [testBit_imgMasks PB _ hP.1]
  constructor
  · rintro ⟨p, hp, e⟩
    have h1 := fl_lt P p
    have h2 := i.isLt
    have hl : fl PB p = l := by omega
    have hi : fl P p = i.val := by omega
    exact ⟨⟨p, hp⟩, hl, Fin.ext hi⟩
  · rintro ⟨p, hp, e⟩
    refine ⟨p.val, p.isLt, ?_⟩
    have e' := congrArg Fin.val e
    simp only [flF] at e'
    rw [hp, e']
    ring

theorem pbBlock_eq_msk (PB l : ℕ) : pbBlock PB l = msk (fld16 (imgMasks idP PB) l) := by
  rw [msk_img isP_idP, perm16_idP, inv_one, one_smul]

theorem smul_sysPB {P : ℕ} (hP : IsP P) (NB PB : ℕ) :
    (perm16 P)⁻¹ • sysPB NB PB =
      (Finset.range NB).image fun l => msk (fld16 (imgMasks P PB) (l + 1)) := by
  rw [sysPB, Finset.smul_finset_def, Finset.image_image]
  congr 1
  funext l
  exact (msk_img hP PB (l + 1)).symm

theorem memb_iff (NB OM m : ℕ) : memb NB OM m = true ↔ ∃ l < NB, fld16 OM l = m := by
  unfold memb
  rw [anyRec_iff (fun l => Nat.beq (fld16 OM l) m) NB]
  simp only [Nat.beq_eq]

theorem allMemb_iff (NB OM M : ℕ) :
    allMemb NB OM M = true ↔ ∀ l < NB, ∃ l' < NB, fld16 OM l' = fld16 M (l + 1) := by
  unfold allMemb
  rw [allRec_iff (fun l => memb NB OM (fld16 M (Nat.succ l))) NB]
  simp only [memb_iff]

theorem allIn_iff (NB BB M : ℕ) :
    allIn NB BB M = true ↔ ∀ l < NB, BB.testBit (fld16 M (l + 1)) = true := by
  unfold allIn
  rw [allRec_iff (fun l => Nat.blt 0 (Nat.land BB (Nat.shiftLeft 1 (fld16 M (Nat.succ l))))) NB]
  have e : ∀ l, Nat.blt 0 (Nat.land BB (Nat.shiftLeft 1 (fld16 M (Nat.succ l)))) =
      bitAt BB (fld16 M (l + 1)) := fun _ => rfl
  simp only [e, bitAt_iff]

theorem bbOK_spec {NB BB OM : ℕ} (h : bbOK NB BB OM = true) (m : ℕ) :
    BB.testBit m = true ↔ ∃ l < NB, fld16 OM l = m := by
  unfold bbOK at h
  rw [Nat.beq_eq] at h
  subst h
  induction NB with
  | zero => simp
  | succ n ih =>
    change (Nat.lor (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun l acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (fld16 OM l))) n)
        (Nat.shiftLeft (nat_lit 1) (fld16 OM n))).testBit m = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih]
    change _ ∨ (1 <<< fld16 OM n).testBit m = true ↔ _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (⟨l, hl, e⟩ | e)
      · exact ⟨l, by omega, e⟩
      · exact ⟨n, by omega, e⟩
    · rintro ⟨l, hl, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact Or.inl ⟨l, hl, e⟩
      · exact Or.inr e

theorem allMemb_of_allIn {NB BB OM M : ℕ} (hbb : bbOK NB BB OM = true) (h : allIn NB BB M = true) :
    allMemb NB OM M = true := by
  rw [allMemb_iff]
  intro l hl
  exact (bbOK_spec hbb _).1 ((allIn_iff NB BB M).1 h l hl)

theorem sys_img {NB PB OM OM' P : ℕ} (hP : IsP P) (hsys : sysPB NB PB = sysOf NB OM)
    (hc : (sysOf NB OM).card = NB) (hc' : (sysOf NB OM').card = NB)
    (h : allMemb NB OM' (imgMasks P PB) = true) :
    (perm16 P)⁻¹ • sysOf NB OM = sysOf NB OM' := by
  rw [← hsys]
  apply Finset.eq_of_subset_of_card_le
  · rw [smul_sysPB hP]
    intro s hs
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨l', hl', e⟩ := (allMemb_iff NB OM' _).1 h l (Finset.mem_range.1 hl)
    exact Finset.mem_image.2 ⟨l', Finset.mem_range.2 hl', by rw [e]⟩
  · rw [Finset.card_smul_finset, hsys, hc, hc']

theorem allIn_sys {NB BB PB OM OMb P : ℕ} (hbb : bbOK NB BB OMb = true) (hP : IsP P)
    (hsys : sysPB NB PB = sysOf NB OM) (hc : (sysOf NB OM).card = NB)
    (hcb : (sysOf NB OMb).card = NB) (h : allIn NB BB (imgMasks P PB) = true) :
    (perm16 P)⁻¹ • sysOf NB OM = sysOf NB OMb :=
  sys_img hP hsys hc hcb (allMemb_of_allIn hbb h)

theorem strictMono_of_succ {a : ℕ → ℕ} {n : ℕ} (h : ∀ l, l + 1 < n → a l < a (l + 1)) :
    ∀ l l', l < l' → l' < n → a l < a l' := by
  intro l l' hll' hl'
  induction l' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hll' with h1 | rfl
    · exact Nat.lt_trans (ih h1 (by omega)) (h k hl')
    · exact h l hl'

theorem sysOf_card {NB OM : ℕ} (hs : ∀ l, l + 1 < NB → fld16 OM l < fld16 OM (l + 1)) :
    (sysOf NB OM).card = NB := by
  rw [sysOf, Finset.card_image_of_injOn, Finset.card_range]
  intro l hl l' hl' e
  have e' := msk_inj (fld16_lt OM l) (fld16_lt OM l') e
  simp only [Finset.coe_range, Set.mem_Iio] at hl hl'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd e' (Nat.ne_of_lt (strictMono_of_succ hs l l' h hl'))
  · exact absurd e' (Nat.ne_of_gt (strictMono_of_succ hs l' l h hl))

theorem pbOK_spec {NB ID PB OM : ℕ} (h : pbOK NB ID PB OM = true) :
    pbTag PB = omTag OM ∧ allMemb NB OM (imgMasks ID PB) = true ∧
      ∀ l, l + 1 < NB → fld16 OM l < fld16 OM (l + 1) := by
  unfold pbOK at h
  rw [andB_iff, andB_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun l hl => ?_⟩
  have := (allRec_iff (fun l => Nat.blt (fld16 OM l) (fld16 OM (Nat.succ l))) _).1 h3 l (by
    change l < NB - 1
    omega)
  simpa using this

theorem omOK_parts {PBT OMT GT HT : ℕ → ℕ} {NB NH PB0 j : ℕ}
    (h : omOK PBT OMT GT HT NB NH PB0 j = true) :
    allMemb NB (OMT j) (imgMasks idP (PBT j)) = true ∧
      (∀ l, l + 1 < NB → fld16 (OMT j) l < fld16 (OMT j) (l + 1)) ∧
      0 < fld16 (OMT j) 0 ∧ Nat.land (OMT j) m112 < 2 ^ (16 * NB) ∧ GT j < NH ∧
      allMemb NB (OMT j) (imgMasks (hP (HT (GT j))) PB0) = true ∧
      (j ≠ 0 → Nat.land (OMT (j - 1)) m112 < Nat.land (OMT j) m112) := by
  unfold omOK at h
  rw [letB_eq, letB_eq] at h
  simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hpb, -, -, h0, hm, hg, hgo, hj⟩ := h
  obtain ⟨-, hpb2, hpb3⟩ := pbOK_spec hpb
  refine ⟨hpb2, hpb3, h0, ?_, hg, hgo, fun hj0 => hj.resolve_left hj0⟩
  have e : Nat.shiftLeft 1 (Nat.mul 16 NB) = 2 ^ (16 * NB) := by
    change 1 <<< (16 * NB) = _
    rw [Nat.one_shiftLeft]
  rw [e] at hm
  exact hm

theorem omOK_sys {PBT OMT GT HT : ℕ → ℕ} {NB NH PB0 j : ℕ}
    (h : omOK PBT OMT GT HT NB NH PB0 j = true) :
    sysPB NB (PBT j) = sysOf NB (OMT j) ∧ (sysOf NB (OMT j)).card = NB := by
  obtain ⟨hmem, hs, h0, -⟩ := omOK_parts h
  have hc := sysOf_card hs
  refine ⟨?_, hc⟩
  have hpos : ∀ l < NB, 0 < fld16 (OMT j) l := fun l hl => by
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · exact h0
    · exact Nat.lt_trans h0 (strictMono_of_succ hs 0 l hl0 hl)
  apply Finset.eq_of_subset_of_card_le
  · intro s hs'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hs'
    obtain ⟨l', hl', e⟩ := (allMemb_iff NB _ _).1 hmem l (Finset.mem_range.1 hl)
    refine Finset.mem_image.2 ⟨l', Finset.mem_range.2 hl', ?_⟩
    rw [pbBlock_eq_msk, e]
  · rw [hc, sysPB, Finset.card_image_of_injOn, Finset.card_range]
    intro l hl l' hl' e
    simp only [Finset.coe_range, Set.mem_Iio] at hl hl'
    obtain ⟨l1, hl1, e1⟩ := (allMemb_iff NB _ _).1 hmem l hl
    have hne : (pbBlock (PBT j) (l + 1)).Nonempty := by
      rw [pbBlock_eq_msk, ← e1]
      exact msk_nonempty (hpos l1 hl1) (fld16_lt _ _)
    obtain ⟨p, hp⟩ := hne
    have hp' := hp
    have e2 : pbBlock (PBT j) (l + 1) = pbBlock (PBT j) (l' + 1) := e
    rw [e2] at hp'
    simp only [pbBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    omega

theorem omOK_g {PBT OMT GT HT : ℕ → ℕ} {NB NH j I0 : ℕ}
    (h : omOK PBT OMT GT HT NB NH (PBT I0) j = true)
    (h0 : omOK PBT OMT GT HT NB NH (PBT I0) I0 = true) (hg : IsP (hP (HT (GT j)))) :
    GT j < NH ∧ (perm16 (hP (HT (GT j))))⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT j) := by
  obtain ⟨-, -, -, -, hgt, hgo, -⟩ := omOK_parts h
  obtain ⟨hs0, hc0⟩ := omOK_sys h0
  exact ⟨hgt, sys_img hg hs0 hc0 (omOK_sys h).2 hgo⟩

theorem sorted_eq {n : ℕ} {a b : ℕ → ℕ} (ha : ∀ l, l + 1 < n → a l < a (l + 1))
    (hb : ∀ l, l + 1 < n → b l < b (l + 1))
    (h : (Finset.range n).image a = (Finset.range n).image b) : ∀ l < n, a l = b l := by
  have hinj : ∀ c : ℕ → ℕ, (∀ l, l + 1 < n → c l < c (l + 1)) →
      ((Finset.range n).image c).card = n := fun c hc => by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro l hl l' hl' e
      simp only [Finset.coe_range, Set.mem_Iio] at hl hl'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · exact absurd e (Nat.ne_of_lt (strictMono_of_succ hc l l' h1 hl'))
      · exact absurd e (Nat.ne_of_gt (strictMono_of_succ hc l' l h1 hl))
  have mono : ∀ c : ℕ → ℕ, (∀ l, l + 1 < n → c l < c (l + 1)) →
      StrictMono (fun l : Fin n => c l.val) := fun c hc l l' hll' =>
    strictMono_of_succ hc l.val l'.val hll' l'.isLt
  have ea := Finset.orderEmbOfFin_unique (hinj a ha) (f := fun l : Fin n => a l.val)
    (fun l => Finset.mem_image.2 ⟨l.val, Finset.mem_range.2 l.isLt, rfl⟩) (mono a ha)
  have eb := Finset.orderEmbOfFin_unique (hinj a ha) (f := fun l : Fin n => b l.val)
    (fun l => by
      rw [h]
      exact Finset.mem_image.2 ⟨l.val, Finset.mem_range.2 l.isLt, rfl⟩) (mono b hb)
  intro l hl
  exact congrArg (fun f : Fin n → ℕ => f ⟨l, hl⟩) (ea.trans eb.symm)

theorem m112_eq {NB OM OM' : ℕ} (hNB : NB ≤ 7) (h : Nat.land OM m112 < 2 ^ (16 * NB))
    (h' : Nat.land OM' m112 < 2 ^ (16 * NB)) (hf : ∀ l < NB, fld16 OM l = fld16 OM' l) :
    Nat.land OM m112 = Nat.land OM' m112 := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 16 * NB
  · have e : ∀ x, (Nat.land x m112).testBit n = x.testBit n := fun x => by
      rw [land_lit x 112 m112 rfl, Nat.testBit_mod_two_pow]
      simp only [Bool.and_eq_right_iff_imp, decide_eq_true_eq]
      intro
      omega
    rw [e, e]
    have h1 := testBit_fld16 OM (n / 16) (n % 16)
    have h2 := testBit_fld16 OM' (n / 16) (n % 16)
    have en : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
    have hk : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
    rw [en] at h1 h2
    simp only [hk, decide_true, Bool.true_and] at h1 h2
    rw [← h1, ← h2, hf (n / 16) (by omega)]
  · have hp : 2 ^ (16 * NB) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem omOK_inj {PBT OMT GT HT : ℕ → ℕ} {NB NH PB0 NO : ℕ} (hNB : NB ≤ 7)
    (h : ∀ j < NO, omOK PBT OMT GT HT NB NH PB0 j = true) :
    ∀ i < NO, ∀ i' < NO, sysOf NB (OMT i) = sysOf NB (OMT i') → i = i' := by
  have hmono : ∀ j, j + 1 < NO → Nat.land (OMT j) m112 < Nat.land (OMT (j + 1)) m112 := by
    intro j hj
    have := (omOK_parts (h (j + 1) hj)).2.2.2.2.2.2 (by omega)
    simpa using this
  intro i hi i' hi' e
  have key : Nat.land (OMT i) m112 = Nat.land (OMT i') m112 := by
    obtain ⟨-, hs, -, hm, -⟩ := omOK_parts (h i hi)
    obtain ⟨-, hs', -, hm', -⟩ := omOK_parts (h i' hi')
    refine m112_eq hNB hm hm' (sorted_eq hs hs' ?_)
    ext m
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have : msk (fld16 (OMT i) l) ∈ sysOf NB (OMT i') :=
        e ▸ Finset.mem_image.2 ⟨l, Finset.mem_range.2 hl, rfl⟩
      obtain ⟨l', hl', e'⟩ := Finset.mem_image.1 this
      exact ⟨l', Finset.mem_range.1 hl', msk_inj (fld16_lt _ _) (fld16_lt _ _) e'⟩
    · rintro ⟨l, hl, rfl⟩
      have : msk (fld16 (OMT i') l) ∈ sysOf NB (OMT i) :=
        e.symm ▸ Finset.mem_image.2 ⟨l, Finset.mem_range.2 hl, rfl⟩
      obtain ⟨l', hl', e'⟩ := Finset.mem_image.1 this
      exact ⟨l', Finset.mem_range.1 hl', msk_inj (fld16_lt _ _) (fld16_lt _ _) e'⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · exact absurd key (Nat.ne_of_lt (strictMono_of_succ hmono i i' h1 hi'))
  · exact absurd key (Nat.ne_of_gt (strictMono_of_succ hmono i' i h1 hi))

theorem nLetter_index {NL TL c : ℕ} (hTL : TL < NL) (hc : c < NL) (hcT : c ≠ TL) :
    ∃ k < NL - 1, Bool.rec (motive := fun _ => ℕ) (Nat.succ k) k (Nat.blt k TL) = c := by
  rcases Nat.lt_or_gt_of_ne hcT with h | h
  · refine ⟨c, by omega, ?_⟩
    have : Nat.blt c TL = true := by
      rw [Nat.blt_eq]
      exact h
    rw [this]
  · refine ⟨c - 1, by omega, ?_⟩
    have : Nat.blt (c - 1) TL = false := by
      cases e : Nat.blt (c - 1) TL
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [this]
    change c - 1 + 1 = c
    omega

theorem omClosOK_spec {LT PBT OMT OHT : ℕ → ℕ} {NL TL NB NO j : ℕ}
    (h : CFSG.KC.Co1M.omClosOK LT PBT OMT OHT NL TL NB NO j = true) (hTL : TL < NL) :
    ∀ c < NL, c ≠ TL → ∃ h' < NO,
      allMemb NB (OMT h') (imgMasks (Nat.land (LT c) m64) (PBT j)) = true := by
  intro c hc hcT
  unfold CFSG.KC.Co1M.omClosOK at h
  rw [letB_eq] at h
  obtain ⟨k, hk, e⟩ := nLetter_index hTL hc hcT
  have := (allRec_iff _ _).1 h k hk
  rw [andB_iff, Nat.blt_eq] at this
  refine ⟨_, this.1, ?_⟩
  rw [← e]
  exact this.2

theorem tgOK_spec {PBT OMT : ℕ → ℕ} {NB I0 TGs ngT : ℕ} (h : tgOK PBT OMT NB I0 TGs ngT = true) :
    ∀ k < ngT, IsP (gk TGs k) ∧ allMemb NB (OMT I0) (imgMasks (gk TGs k) (PBT I0)) = true := by
  intro k hk
  unfold tgOK at h
  have := (allRec_iff _ _).1 h k hk
  rw [andB_iff] at this
  exact ⟨isP_of_isPerm this.1, this.2⟩

theorem constOK_spec {OMT : ℕ → ℕ} {NB NO I0 BB BASEM NL TL ND ALIVE : ℕ}
    (h : constOK OMT NB NO I0 BB BASEM NL TL ND ALIVE = true) :
    0 < NB ∧ NB ≤ 7 ∧ I0 < NO ∧ bbOK NB BB (OMT I0) = true ∧ TL < NL ∧ ALIVE < 2 ^ ND ∧
      ALIVE.testBit 0 = true ∧ 0 < ND := by
  unfold constOK at h
  simp only [andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8⟩ := h
  have e : Nat.shiftLeft 1 ND = 2 ^ ND := by
    change 1 <<< ND = _
    rw [Nat.one_shiftLeft]
  rw [e] at h7
  rw [bitAt_iff] at h8
  refine ⟨h1, h2, h3, h4, h6, h7, h8, ?_⟩
  rcases Nat.eq_zero_or_pos ND with h0 | h0
  · subst h0
    have : ALIVE = 0 := by omega
    subst this
    exact absurd h8 (by decide)
  · exact h0

theorem letOK_spec {LT : ℕ → ℕ} {TL c : ℕ} (h : letOK LT TL c = true) :
    (c = TL → ltN (LT c) = false) ∧ (c ≠ TL → ltN (LT c) = true ∧ IsP (Nat.land (LT c) m64)) := by
  unfold letOK at h
  rw [letB_eq, brec_eq] at h
  split_ifs at h with h1
  · rw [Nat.beq_eq] at h1
    refine ⟨fun _ => ?_, fun h2 => absurd h1 h2⟩
    simpa using h
  · rw [Nat.beq_eq] at h1
    rw [andB_iff] at h
    exact ⟨fun h2 => absurd h2 h1, fun _ => ⟨h.1, isP_of_isPerm h.2⟩⟩

@[expose] noncomputable def wc (LT : ℕ → ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc c => pmul acc (Nat.land (LT c) m64)) idP

theorem foldl_spec (LT : ℕ → ℕ) : ∀ (w : List ℕ) (acc : ℕ), IsP acc →
    (∀ c ∈ w, IsP (Nat.land (LT c) m64)) →
    IsP (w.foldl (fun acc c => pmul acc (Nat.land (LT c) m64)) acc) ∧
      perm16 (w.foldl (fun acc c => pmul acc (Nat.land (LT c) m64)) acc) =
        perm16 acc * (w.map fun c => perm16 (Nat.land (LT c) m64)).prod
  | [], acc, ha, _ => ⟨ha, by simp⟩
  | c :: w, acc, ha, hw => by
    have hc := hw c (by simp)
    obtain ⟨h1, h2⟩ := foldl_spec LT w (pmul acc _) (isP_pmul ha hc)
      (fun d hd => hw d (List.mem_cons_of_mem c hd))
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, perm16_pmul ha hc, List.map_cons, List.prod_cons, mul_assoc]

theorem wc_spec {LT : ℕ → ℕ} {w : List ℕ} (hw : ∀ c ∈ w, IsP (Nat.land (LT c) m64)) :
    IsP (wc LT w) ∧ perm16 (wc LT w) = (w.map fun c => perm16 (Nat.land (LT c) m64)).prod := by
  have := foldl_spec LT w idP isP_idP hw
  rw [perm16_idP, one_mul] at this
  exact this

theorem pmul_idP_left {a : ℕ} (ha : IsP a) : pmul idP a = a :=
  perm16_inj (isP_pmul isP_idP ha) ha (by rw [perm16_pmul isP_idP ha, perm16_idP, one_mul])

theorem wc_append {LT : ℕ → ℕ} {u v : List ℕ} (hu : ∀ c ∈ u, IsP (Nat.land (LT c) m64))
    (hv : ∀ c ∈ v, IsP (Nat.land (LT c) m64)) : wc LT (u ++ v) = pmul (wc LT u) (wc LT v) := by
  have huv : ∀ c ∈ u ++ v, IsP (Nat.land (LT c) m64) := fun c hc => by
    rcases List.mem_append.1 hc with h | h
    · exact hu c h
    · exact hv c h
  apply perm16_inj (wc_spec huv).1 (isP_pmul (wc_spec hu).1 (wc_spec hv).1)
  rw [(wc_spec huv).2, perm16_pmul (wc_spec hu).1 (wc_spec hv).1, (wc_spec hu).2, (wc_spec hv).2,
    List.map_append, List.prod_append]

theorem wc_single {LT : ℕ → ℕ} {c : ℕ} (hc : IsP (Nat.land (LT c) m64)) :
    wc LT [c] = Nat.land (LT c) m64 :=
  pmul_idP_left hc

theorem hdrOK_spec {HT LT : ℕ → ℕ} {NL h : ℕ} (hh : hdrOK HT LT NL h = true) :
    hP (HT h) = idP ∨
      (hA (HT h) < NL ∧ ltN (LT (hA (HT h))) = true ∧ hP (HT h) = Nat.land (LT (hA (HT h))) m64) ∨
      (hA (HT h) < h ∧ hB (HT h) < h ∧
        hP (HT h) = pmul (hP (HT (hA (HT h)))) (hP (HT (hB (HT h))))) := by
  unfold hdrOK at hh
  simp only [letB_eq, brec_eq] at hh
  split_ifs at hh with h0 h1
  · left
    simpa using hh
  · right
    left
    simpa [andB_iff] using hh
  · right
    right
    simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hh
    exact hh.2

theorem hdr_word {HT LT : ℕ → ℕ} {NL TL NH : ℕ} (hh : ∀ h < NH, hdrOK HT LT NL h = true)
    (hl : ∀ c < NL, letOK LT TL c = true) :
    ∀ h < NH, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = hP (HT h) := by
  have hP' : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → ∀ c ∈ w, IsP (Nat.land (LT c) m64) :=
    fun w hw c hc => ((letOK_spec (hl c (hw c hc).1)).2 (hw c hc).2).2
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hlt
    rcases hdrOK_spec (hh h hlt) with e | ⟨ha, hn, e⟩ | ⟨ha, hb, e⟩
    · exact ⟨[], by simp, by rw [e]; rfl⟩
    · have hTL : hA (HT h) ≠ TL := fun e' => by
        have := (letOK_spec (hl _ ha)).1 e'
        rw [this] at hn
        exact Bool.false_ne_true hn
      have hw : ∀ c ∈ [hA (HT h)], c < NL ∧ c ≠ TL := by simpa using ⟨ha, hTL⟩
      refine ⟨[hA (HT h)], hw, ?_⟩
      rw [e, wc_single (hP' _ hw _ (by simp))]
    · obtain ⟨wa, hwa, ea⟩ := ih _ ha (by omega)
      obtain ⟨wb, hwb, eb⟩ := ih _ hb (by omega)
      have hw : ∀ c ∈ wa ++ wb, c < NL ∧ c ≠ TL := fun c hc => by
        rcases List.mem_append.1 hc with h' | h'
        · exact hwa c h'
        · exact hwb c h'
      refine ⟨wa ++ wb, hw, ?_⟩
      rw [wc_append (hP' _ hwa) (hP' _ hwb), ea, eb, e]

section Words

variable {G : Type*} [Group G]

@[expose] noncomputable def bvF (f : ℕ → G) (W n : ℕ) : G :=
  ((List.range n).map fun q => f (wLet W q)).prod

theorem bvF_succ (f : ℕ → G) (W n : ℕ) : bvF f W (n + 1) = bvF f W n * f (wLet W n) := by
  unfold bvF
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bvF_eq (f : ℕ → G) (W n : ℕ) :
    bvF f W n = ((List.range n).map fun i => f (W / 256 ^ i % 256)).prod := by
  simp only [bvF, wLet_eq]

theorem bvF_concat (f : ℕ → G) {A B p q : ℕ} (hA : A < 256 ^ p) :
    bvF f (A + B * 256 ^ p) (p + q) = bvF f A p * bvF f B q := by
  rw [bvF_eq, bvF_eq, bvF_eq, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [byte_concat hA]
    simp only [hi, ↓reduceIte]
  · apply List.map_congr_left
    intro j _
    have hj : ¬p + j < p := by omega
    simp only [Function.comp_apply, byte_concat hA, hj, ↓reduceIte, Nat.add_sub_cancel_left]

theorem bvF_one (f : ℕ → G) {c : ℕ} (hc : c < 256) : bvF f c 1 = f c := by
  simp [bvF_eq, Nat.mod_eq_of_lt hc]

theorem invRelOK_spec {RT : ℕ → ℕ} {NL NR IH : ℕ} (h : invRelOK RT NL NR IH = true)
    (hNL : NL < 256) : ∀ c < NL, ∃ r < NR, rN (RT r) = 2 ∧ wLet (rW (RT r)) 0 = c ∧
      wLet (rW (RT r)) 1 = c := by
  intro c hc
  unfold invRelOK at h
  have := (allRec_iff _ _).1 h c hc
  rw [andB_iff, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨_, h1, ?_⟩
  rw [h2]
  have e : Nat.add 2 (Nat.shiftLeft (Nat.add c (Nat.mul 256 c)) 8) = 2 + (c + 256 * c) * 2 ^ 8 := by
    change 2 + (c + 256 * c) <<< 8 = _
    rw [Nat.shiftLeft_eq]
  rw [e]
  have e1 : rN (2 + (c + 256 * c) * 2 ^ 8) = 2 := by
    unfold rN
    rw [land_lit _ 8 255 rfl, Nat.add_mul_mod_self_right]
    rfl
  have e2 : rW (2 + (c + 256 * c) * 2 ^ 8) = c + 256 * c := by
    unfold rW
    rw [shr_eq, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (by norm_num),
      Nat.zero_add]
  have hc256 : c < 256 := by omega
  rw [e1, e2, wLet_eq, wLet_eq, pow_zero, Nat.div_one, pow_one,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 256), Nat.div_eq_of_lt hc256, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc256]
  exact ⟨rfl, rfl, rfl⟩

theorem x_invol {RT : ℕ → ℕ} {NL NR IH : ℕ} (h : invRelOK RT NL NR IH = true) (hNL : NL < 256)
    (x : ℕ → G) (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1) :
    ∀ c < NL, x c * x c = 1 := by
  intro c hc
  obtain ⟨r, hr, e1, e2, e3⟩ := invRelOK_spec h hNL c hc
  have := hrels r hr
  rw [e1, bvF] at this
  simpa [List.range_succ, e2, e3] using this

theorem refCount_succ (TL W q : ℕ) : refCount TL W (q + 1) =
    if wLet W q = 255 ∨ wLet W q = TL then refCount TL W q + 1 else refCount TL W q := by
  change Bool.rec (motive := fun _ => ℕ) (refCount TL W q) (Nat.succ (refCount TL W q))
    (orB (Nat.beq (wLet W q) 255) (Nat.beq (wLet W q) TL)) = _
  simp only [brec_eq, orB_iff, Nat.beq_eq, Nat.succ_eq_add_one]

theorem refCount_le (TL W : ℕ) : ∀ q, refCount TL W q ≤ q
  | 0 => le_refl _
  | q + 1 => by
    rw [refCount_succ]
    have := refCount_le TL W q
    split_ifs <;> omega

theorem refCount_mono (TL W : ℕ) {q q' : ℕ} (h : q ≤ q') : refCount TL W q ≤ refCount TL W q' := by
  induction q' with
  | zero =>
    rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h1 | h1
    · rw [refCount_succ]
      have := ih (by omega)
      split_ifs <;> omega
    · rw [h1]

theorem evalN_succ (LT : ℕ → ℕ) (NL W q : ℕ) : evalN LT NL W (q + 1) =
    if wLet W q < NL ∧ ltN (LT (wLet W q)) = true then
      pmul (evalN LT NL W q) (Nat.land (LT (wLet W q)) m64) else 0 := by
  change Bool.rec (motive := fun _ => ℕ) 0 (pmul (evalN LT NL W q) (Nat.land (LT (wLet W q)) m64))
    (andB (Nat.blt (wLet W q) NL) (ltN (LT (wLet W q)))) = _
  simp only [brec_eq, andB_iff, Nat.blt_eq]

theorem relOK_spec {RT LT : ℕ → ℕ} {NL TL r : ℕ} (h : relOK RT LT NL TL r = true) :
    rW (RT r) < 2 ^ (8 * rN (RT r)) ∧ (∀ q < rN (RT r), wLet (rW (RT r)) q < NL) ∧
      (0 < refCount TL (rW (RT r)) (rN (RT r)) ∨ evalN LT NL (rW (RT r)) (rN (RT r)) = idP) := by
  unfold relOK at h
  rw [letB_eq] at h
  simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun q hq => ?_, h3⟩
  · have e : Nat.shiftLeft 1 (Nat.mul 8 (rN (RT r))) = 2 ^ (8 * rN (RT r)) := by
      change 1 <<< (8 * rN (RT r)) = _
      rw [Nat.one_shiftLeft]
    rw [e] at h1
    exact h1
  · have := (allRec_iff (fun q => Nat.blt (wLet (rW (RT r)) q) NL) _).1 h2 q hq
    simpa using this

theorem L_invol {RT LT : ℕ → ℕ} {NL TL NR IH : ℕ} (h : invRelOK RT NL NR IH = true)
    (hNL : NL < 255) (hrel : ∀ r < NR, relOK RT LT NL TL r = true)
    (hl : ∀ c < NL, letOK LT TL c = true) :
    ∀ c < NL, c ≠ TL → pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP := by
  intro c hc hcT
  obtain ⟨r, hr, e1, e2, e3⟩ := invRelOK_spec h (by omega) c hc
  obtain ⟨-, -, h3⟩ := relOK_spec (hrel r hr)
  obtain ⟨hn, hP⟩ := (letOK_spec (hl c hc)).2 hcT
  rw [e1] at h3
  have hc0 : refCount TL (rW (RT r)) 2 = 0 := by
    rw [refCount_succ, refCount_succ, e2, e3]
    have : ¬(c = 255 ∨ c = TL) := by omega
    simp only [this, ↓reduceIte]
    rfl
  rw [hc0] at h3
  have e : evalN LT NL (rW (RT r)) 2 = pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) := by
    rw [evalN_succ, evalN_succ, e2, e3]
    simp only [hc, hn, and_self, ↓reduceIte]
    have e0 : evalN LT NL (rW (RT r)) 0 = idP := rfl
    rw [e0, pmul_idP_left hP]
  rw [← e]
  exact h3.resolve_left (lt_irrefl 0)

theorem rval_eq {RT LT : ℕ → ℕ} {NL TL r : ℕ} (h : relOK RT LT NL TL r = true) (hNL : NL < 255)
    (x : ℕ → G) :
    bvF (fun c => if c = 255 then 1 else x c) (rW (RT r)) (rN (RT r)) =
      bvF x (rW (RT r)) (rN (RT r)) := by
  obtain ⟨-, h2, -⟩ := relOK_spec h
  unfold bvF
  congr 1
  apply List.map_congr_left
  intro q hq
  have := h2 q (List.mem_range.1 hq)
  have hne : wLet (rW (RT r)) q ≠ 255 := by omega
  simp only [hne, ↓reduceIte]

theorem invSelfOK_spec {INV INV8 NL : ℕ} (h : invSelfOK INV INV8 NL = true) :
    NL < 255 ∧ ∀ c < 256,
      (c < NL → inv16 INV c = c ∧ wLet INV8 c = c) ∧
      (NL ≤ c → c = 255 → inv16 INV c = 255) ∧
      (NL ≤ c → c ≠ 255 → inv16 INV c = 65535) := by
  unfold invSelfOK at h
  obtain ⟨hL, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, hloop⟩ := (andB_iff _ _).1 h
  rw [Nat.blt_eq] at hL
  refine ⟨hL, fun c hc => ?_⟩
  have hc' := (allRec2_iff (fun c => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (inv16 INV c) (nat_lit 65535)) (Nat.beq (wLet INV8 c) (nat_lit 254)))
        (andB (Nat.beq (inv16 INV c) (nat_lit 255)) (Nat.beq (wLet INV8 c) (nat_lit 255)))
        (Nat.beq c (nat_lit 255)))
      (andB (Nat.beq (inv16 INV c) c) (Nat.beq (wLet INV8 c) c))
      (Nat.blt c NL)) (nat_lit 256)).1 hloop c hc
  rw [brec_eq, brec_eq] at hc'
  refine ⟨fun hcL => ?_, fun hcL hc255 => ?_, fun hcL hc255 => ?_⟩
  · rw [ite_eq_left (by simpa using hcL)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'
  · rw [ite_eq_right (by simpa using hcL), ite_eq_left (by simpa using hc255)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'.1
  · rw [ite_eq_right (by simpa using hcL), ite_eq_right (by simpa using hc255)] at hc'
    simp only [andB_iff, Nat.beq_eq] at hc'
    exact hc'.1

theorem lettersOK_spec {INV INV8 NL W n : ℕ} (hinv : invSelfOK INV INV8 NL = true)
    (h : lettersOK INV W n = true) : ∀ i < n, wLet W i < NL ∨ wLet W i = 255 := by
  intro i hi
  have h1 := (allRec_iff _ n).1 h i hi
  rw [Nat.blt_eq] at h1
  obtain ⟨-, hc⟩ := invSelfOK_spec hinv
  obtain ⟨-, -, h3⟩ := hc _ (wLet_lt W i)
  rcases Nat.lt_or_ge (wLet W i) NL with h' | h'
  · exact Or.inl h'
  · by_cases h'' : wLet W i = 255
    · exact Or.inr h''
    · rw [h3 h' h''] at h1
      exact absurd h1 (lt_irrefl _)

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | x :: l => enc l * 256 + (x + 1)

@[expose] noncomputable def lval (f : ℕ → G) (l : List ℕ) : G := (l.reverse.map f).prod

theorem lval_cons (f : ℕ → G) (x : ℕ) (l : List ℕ) : lval f (x :: l) = lval f l * f x := by
  simp [lval, List.reverse_cons, List.map_append, List.prod_append]

theorem freeRed_spec (f : ℕ → G) (hf : f 255 = 1) {INV INV8 NL W n : ℕ}
    (hinv : invSelfOK INV INV8 NL = true) (hx : ∀ c < NL, f c * f c = 1)
    (hlet : lettersOK INV W n = true) : ∀ i ≤ n, ∃ l : List ℕ,
      freeRed INV8 W i = enc l ∧ (∀ y ∈ l, y < NL) ∧ lval f l = bvF f W i
  | 0, _ => ⟨[], rfl, by simp, rfl⟩
  | i + 1, hi => by
    obtain ⟨l, hl, hlL, hlv⟩ := freeRed_spec f hf hinv hx hlet i (by omega)
    obtain ⟨hL, hc⟩ := invSelfOK_spec hinv
    have hxi := lettersOK_spec hinv hlet i (by omega)
    have e : freeRed INV8 W (i + 1) = Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Nat.add (Nat.mul (freeRed INV8 W i) 256) (Nat.succ (wLet W i)))
        (Nat.shiftRight (freeRed INV8 W i) 8)
        (andB (Nat.blt 0 (freeRed INV8 W i))
          (Nat.beq (Nat.land (freeRed INV8 W i) 255) (Nat.succ (wLet INV8 (wLet W i))))))
      (freeRed INV8 W i) (Nat.beq (wLet W i) 255) := rfl
    rw [e, brec_eq, bvF_succ, ← hlv, hl]
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, hf, mul_one]
      exact ⟨l, rfl, hlL, rfl⟩
    · rw [Nat.beq_eq] at h255
      have hxL : wLet W i < NL := hxi.resolve_right h255
      obtain ⟨-, h8⟩ := (hc _ (wLet_lt W i)).1 hxL
      rw [h8, brec_eq]
      have hpush : ∃ l' : List ℕ, Nat.add (Nat.mul (enc l) 256) (Nat.succ (wLet W i)) = enc l' ∧
          (∀ y ∈ l', y < NL) ∧ lval f l' = lval f l * f (wLet W i) := by
        refine ⟨wLet W i :: l, rfl, ?_, lval_cons f _ _⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxL
        · exact hlL y hy
      split_ifs with hcond
      · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at hcond
        obtain ⟨hpos, htop⟩ := hcond
        rcases l with _ | ⟨y, l'⟩
        · exact absurd hpos (by simp [enc])
        · have e1 : Nat.land (enc (y :: l')) 255 = y + 1 := by
            have hy := hlL y (by simp)
            change (enc l' * 256 + (y + 1)) &&& (2 ^ 8 - 1) = _
            rw [Nat.and_two_pow_sub_one_eq_mod]
            omega
          rw [e1] at htop
          have hyx : y = wLet W i := by
            change y + 1 = wLet W i + 1 at htop
            exact Nat.succ.inj htop
          refine ⟨l', ?_, fun z hz => hlL z (by simp [hz]), ?_⟩
          · change (enc l' * 256 + (y + 1)) >>> 8 = enc l'
            rw [Nat.shiftRight_eq_div_pow]
            omega
          · rw [lval_cons, hyx, mul_assoc, hx _ hxL, mul_one]
      · exact hpush

theorem freeRed_zero (f : ℕ → G) (hf : f 255 = 1) {INV INV8 NL W n : ℕ}
    (hinv : invSelfOK INV INV8 NL = true) (hx : ∀ c < NL, f c * f c = 1)
    (hlet : lettersOK INV W n = true) (h0 : freeRed INV8 W n = 0) : bvF f W n = 1 := by
  obtain ⟨l, hl, -, hv⟩ := freeRed_spec f hf hinv hx hlet n le_rfl
  rw [← hv]
  rcases l with _ | ⟨y, l'⟩
  · rfl
  · rw [h0] at hl
    simp [enc] at hl

theorem strip_spec (f : ℕ → G) (hf : f 255 = 1) (W : ℕ) : ∀ i,
    (strip W i).1 < 256 ^ (strip W i).2 ∧ bvF f (strip W i).1 (strip W i).2 = bvF f W i
  | 0 => ⟨by simp [strip], rfl⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := strip_spec f hf W i
    have e : strip W (i + 1) = Bool.rec (motive := fun _ => ℕ × ℕ)
        (Nat.lor (strip W i).1 (Nat.shiftLeft (wLet W i) (Nat.mul 8 (strip W i).2)),
          Nat.succ (strip W i).2)
        ((strip W i).1, (strip W i).2) (Nat.beq (wLet W i) 255) := rfl
    rw [e, brec_eq, bvF_succ, ← h2]
    split_ifs with h255
    · rw [Nat.beq_eq] at h255
      rw [h255, hf, mul_one]
      exact ⟨h1, rfl⟩
    · have hlt : (strip W i).1 < 2 ^ (Nat.mul 8 (strip W i).2) := by
        change _ < 2 ^ (8 * _)
        rwa [two_pow_eight_mul]
      dsimp only
      rw [lor_shl hlt]
      change (strip W i).1 + wLet W i * 2 ^ (8 * (strip W i).2) < 256 ^ ((strip W i).2 + 1) ∧
        bvF f ((strip W i).1 + wLet W i * 2 ^ (8 * (strip W i).2)) ((strip W i).2 + 1) = _
      rw [two_pow_eight_mul, bvF_concat f h1, bvF_one f (wLet_lt W i)]
      refine ⟨?_, rfl⟩
      have := wLet_lt W i
      calc (strip W i).1 + wLet W i * 256 ^ (strip W i).2
          < 256 ^ (strip W i).2 + wLet W i * 256 ^ (strip W i).2 := by omega
        _ = (wLet W i + 1) * 256 ^ (strip W i).2 := by ring
        _ ≤ 256 * 256 ^ (strip W i).2 := Nat.mul_le_mul_right _ (by omega)
        _ = 256 ^ ((strip W i).2 + 1) := by ring

theorem rot_eq {r n s : ℕ} (hr : r < 256 ^ n) (hs : s ≤ n) :
    rot r n s = r / 256 ^ s + r % 256 ^ s * 256 ^ (n - s) := by
  unfold rot
  rw [land_mask, shr_eq]
  change r / 2 ^ (8 * s) ||| (r % 2 ^ (8 * s)) <<< (8 * (n - s)) = _
  have hA : r / 2 ^ (8 * s) < 2 ^ (8 * (n - s)) := by
    rw [two_pow_eight_mul, two_pow_eight_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.sub_add_cancel hs]
    exact hr
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hA, Nat.shiftLeft_eq, two_pow_eight_mul,
    two_pow_eight_mul]
  ring

theorem bvF_rot (f : ℕ → G) {r n s : ℕ} (hr : r < 256 ^ n) (hs : s < n) (h1 : bvF f r n = 1) :
    bvF f (rot r n s) n = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = s + d := ⟨n - s, by omega⟩
  rw [rot_eq hr (by omega), Nat.add_sub_cancel_left]
  have hA : r / 256 ^ s < 256 ^ d := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm d s]
    exact hr
  have hB : r % 256 ^ s < 256 ^ s := Nat.mod_lt _ (by positivity)
  have hr' : r = r % 256 ^ s + r / 256 ^ s * 256 ^ s := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div r _).symm
  rw [hr', bvF_concat f hB] at h1
  rw [Nat.add_comm s d, bvF_concat f hA]
  exact mul_eq_one_comm.mp h1

theorem wRel_sound (f : ℕ → G) (hf : f 255 = 1) {INV INV8 NL W n r m : ℕ}
    (hinv : invSelfOK INV INV8 NL = true) (hx : ∀ c < NL, f c * f c = 1)
    (h : wRel INV INV8 W n r m = true) (hr : r < 2 ^ (8 * m)) (h1 : bvF f r m = 1) :
    bvF f W n = 1 := by
  unfold wRel at h
  simp only [andB_iff, orB_iff, Nat.beq_eq] at h
  obtain ⟨hlet, -, hfr | hrot⟩ := h
  · exact freeRed_zero f hf hinv hx hlet hfr
  · unfold isRelRot at hrot
    change andB (Nat.beq (strip W n).2 m) (isRot r m (strip W n).1) = true at hrot
    simp only [andB_iff, Nat.beq_eq] at hrot
    obtain ⟨hk, hrot⟩ := hrot
    obtain ⟨s, hs, hseq⟩ := (anyRec_iff _ m).1 hrot
    rw [Nat.beq_eq] at hseq
    rw [← (strip_spec f hf W n).2, hk, ← hseq]
    rw [two_pow_eight_mul] at hr
    exact bvF_rot f hr hs h1

theorem lettersD_spec {LT : ℕ → ℕ} {NL TL W n : ℕ} (h : lettersD LT NL TL W n = true) :
    ∀ q < n, wLet W q = 255 ∨ wLet W q = TL ∨ (wLet W q < NL ∧ ltN (LT (wLet W q)) = true) := by
  intro q hq
  have := (allRec_iff _ n).1 h q hq
  simpa [orB_iff, andB_iff] using this

theorem wordsOK_sound {WT RT LT : ℕ → ℕ} {INV INV8 NL TL NR m Hs : ℕ}
    (hinv : invSelfOK INV INV8 NL = true) (h : wordsOK WT RT LT INV INV8 NL TL NR m Hs = true)
    (hR : ∀ r < NR, rW (RT r) < 2 ^ (8 * rN (RT r))) (f : ℕ → G) (hf : f 255 = 1)
    (hx : ∀ c < NL, f c * f c = 1) (hrels : ∀ r < NR, bvF f (rW (RT r)) (rN (RT r)) = 1) :
    ∀ t < m, lettersD LT NL TL (wW (WT t)) (wN (WT t)) = true ∧
      refCount TL (wW (WT t)) (wN (WT t)) = wNr (WT t) ∧ bvF f (wW (WT t)) (wN (WT t)) = 1 := by
  intro t ht
  unfold wordsOK at h
  have := hintLoop (fun t H => (fun w r => andB (lettersD LT NL TL (wW w) (wN w))
      (andB (Nat.beq (refCount TL (wW w) (wN w)) (wNr w))
        (andB (Nat.blt (Nat.land H (nat_lit 65535)) NR)
          (wRel INV INV8 (wW w) (wN w) (rW r) (rN r)))))
      (WT t) (RT (Nat.land H (nat_lit 65535)))) m 16 m le_rfl Hs h t ht
  rw [Nat.sub_self, Nat.zero_add] at this
  dsimp only at this
  simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨h1, h2, wRel_sound f hf hinv hx h4 (hR _ h3) (hrels _ h3)⟩

end Words

theorem recOK_spec {ND NO R : ℕ} (h : DceS.recOK ND NO R = true) :
    dD R < ND ∧ dDp R < ND ∧ dJ R ≤ NO ∧ IsP (dP R) := by
  unfold DceS.recOK dRecOK at h
  simp only [andB_iff, Nat.blt_eq, Nat.ble_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, isP_of_isPerm h.2.2.2⟩

theorem dD_lt (R : ℕ) : dD R < 2 ^ 14 := by
  unfold dD
  rw [land_lit _ 14 16383 rfl]
  exact Nat.mod_lt _ (by positivity)

theorem dDp_lt (R : ℕ) : dDp R < 2 ^ 14 := by
  unfold dDp
  rw [land_lit _ 14 16383 rfl]
  exact Nat.mod_lt _ (by positivity)

theorem low39 {R : ℕ} (h : Nat.land R 549755813887 = 0) : dD R = 0 ∧ dJ R = 0 ∧ dDp R = 0 := by
  rw [land_lit R 39 549755813887 rfl] at h
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  unfold dD dJ dDp
  rw [land_lit _ 14 16383 rfl, land_lit _ 11 2047 rfl, land_lit _ 14 16383 rfl, shr_eq, shr_eq]
  have e1 : 2 ^ 39 * m = 2 ^ 14 * (2 ^ 25 * m) := by ring
  have e2 : 2 ^ 39 * m = 2 ^ 14 * (2 ^ 11 * (2 ^ 14 * m)) := by ring
  have e3 : 2 ^ 39 * m = 2 ^ 25 * (2 ^ 14 * m) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Nat.mul_mod_right]
  · rw [e2, Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]
  · rw [e3, Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]

theorem shl_or_shl (a b j k : ℕ) (ha : a < 2 ^ k) :
    a <<< j ||| b <<< (k + j) = (a + b * 2 ^ k) <<< j := by
  rw [Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib]
  congr 1
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem mkW_eq {D P ri : ℕ} (own : ℕ) (hD : D < 2 ^ 14) (hP : P < 2 ^ 64) (hr : ri < 2 ^ 8) :
    mkW D P ri own = D + (P + (ri + own * 2 ^ 8) * 2 ^ 64) * 2 ^ 14 := by
  unfold mkW
  have e1 : Nat.lor (Nat.shiftLeft ri 78) (Nat.shiftLeft own 86) = (ri + own * 2 ^ 8) <<< 78 := by
    change ri <<< 78 ||| own <<< (8 + 78) = _
    exact shl_or_shl ri own 78 8 hr
  have e2 : Nat.lor (Nat.shiftLeft P 14) ((ri + own * 2 ^ 8) <<< 78) =
      (P + (ri + own * 2 ^ 8) * 2 ^ 64) <<< 14 := by
    change P <<< 14 ||| (ri + own * 2 ^ 8) <<< (64 + 14) = _
    exact shl_or_shl P _ 14 64 hP
  rw [e1, e2]
  change D ||| (P + (ri + own * 2 ^ 8) * 2 ^ 64) <<< 14 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hD, Nat.shiftLeft_eq, Nat.add_comm]

private theorem sD_eq (st : ℕ) : DceS.sD st = Nat.land st 16383 := rfl
private theorem sP_eq (st : ℕ) : DceS.sP st = Nat.land (Nat.shiftRight st 14) m64 := rfl
private theorem sRi_eq (st : ℕ) : sRi st = Nat.land (Nat.shiftRight st 78) 255 := rfl
private theorem sOwn_eq (st : ℕ) : sOwn st = Nat.shiftRight st 86 := rfl
private theorem sI_eq (S : ℕ) : sI S = Nat.land S m32 := rfl
private theorem sN_eq (S : ℕ) : sN S = Nat.shiftRight S 32 := rfl

theorem mkW_dec {D P ri own : ℕ} (hD : D < 2 ^ 14) (hP : P < 2 ^ 64) (hr : ri < 2 ^ 8) :
    DceS.sD (mkW D P ri own) = D ∧ DceS.sP (mkW D P ri own) = P ∧ sRi (mkW D P ri own) = ri ∧
      sOwn (mkW D P ri own) = own := by
  rw [mkW_eq own hD hP hr]
  have h14 : (D + (P + (ri + own * 2 ^ 8) * 2 ^ 64) * 2 ^ 14) / 2 ^ 14 =
      P + (ri + own * 2 ^ 8) * 2 ^ 64 := by
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hD, Nat.zero_add]
  have h64 : (P + (ri + own * 2 ^ 8) * 2 ^ 64) / 2 ^ 64 = ri + own * 2 ^ 8 := by
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hP, Nat.zero_add]
  have h8 : (ri + own * 2 ^ 8) / 2 ^ 8 = own := by
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hr, Nat.zero_add]
  have h78 : ∀ x : ℕ, x / 2 ^ 78 = x / 2 ^ 14 / 2 ^ 64 := fun x => by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  have h86 : ∀ x : ℕ, x / 2 ^ 86 = x / 2 ^ 14 / 2 ^ 64 / 2 ^ 8 := fun x => by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, ← pow_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sD_eq, land_lit _ 14 16383 rfl, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hD]
  · rw [sP_eq, land_lit _ 64 m64 rfl, shr_eq, h14, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hP]
  · rw [sRi_eq, land_lit _ 8 255 rfl, shr_eq, h78, h14, h64, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr]
  · rw [sOwn_eq, shr_eq, h86, h14, h64, h8]

theorem mkS_eq {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) : mkS i nx = i + nx * 2 ^ 32 := lor_shl hi

theorem mkS_dec {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) : sI (mkS i nx) = i ∧ sN (mkS i nx) = nx := by
  rw [mkS_eq nx hi]
  refine ⟨?_, ?_⟩
  · rw [sI_eq, land_lit _ 32 m32 rfl, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · rw [sN_eq, shr_eq, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem mkS_wrap (nx : ℕ) : mkS (2 ^ 32) nx = mkS 0 (Nat.lor 1 nx) := by
  unfold mkS
  change 2 ^ 32 ||| nx <<< 32 = 0 ||| (1 ||| nx) <<< 32
  rw [Nat.zero_or, Nat.shiftLeft_or_distrib, Nat.one_shiftLeft]

theorem one_le_lor (nx : ℕ) : 1 ≤ Nat.lor 1 nx := by
  have h : (Nat.lor 1 nx).testBit 0 = true := by
    rw [Nat.lor_eq, Nat.testBit_or]
    simp
  have := Nat.ge_two_pow_of_testBit h
  simpa using this

@[expose] def RStep (PBT : ℕ → ℕ) (NB BB c R D P D' P' : ℕ) : Prop :=
  (D = dD R ∧ D' = dDp R ∧ P' = pmul (dP R) P ∧
    (c = 255 ∧ dJ R = 0 ∨ c ≠ 255 ∧ 0 < dJ R ∧ allIn NB BB (imgMasks P (PBT (dJ R - 1))) = true)) ∨
  (D = dDp R ∧ D' = dD R ∧ P' = pmul (pinv (dP R)) P ∧
    (c = 255 ∧ dJ R = 0 ∨ c ≠ 255 ∧ 0 < dJ R ∧ allIn NB BB (imgMasks P' (PBT (dJ R - 1))) = true))

theorem refApply_spec {PBT : ℕ → ℕ} {NB BB c R dir own D P ri o : ℕ} (hD : D < 2 ^ 14)
    (hP : P < 2 ^ 64) (hr : ri < 2 ^ 8)
    (hne : refApply PBT NB BB c R dir own (mkW D P ri o) ≠ 0) :
    ∃ D' P', refApply PBT NB BB c R dir own (mkW D P ri o) = mkW D' P' (ri + 1) own ∧
      D' < 2 ^ 14 ∧ P' < 2 ^ 64 ∧ RStep PBT NB BB c R D P D' P' := by
  obtain ⟨eD, eP, eR, -⟩ := mkW_dec (own := o) hD hP hr
  unfold refApply at hne ⊢
  rw [eD, eP, eR] at hne ⊢
  simp only [strictN_eq, brec_eq, andB_iff, Nat.beq_eq, Nat.blt_eq] at hne ⊢
  by_cases hc : c = 255
  · by_cases hd : dir = 1
    · simp only [hc, hd, ↓reduceIte] at hne ⊢
      split_ifs at hne ⊢ with hcond
      · exact ⟨_, _, rfl, dD_lt R, pmul_lt _ _, Or.inr ⟨hcond.1, rfl, rfl, Or.inl ⟨rfl, hcond.2⟩⟩⟩
      · exact absurd rfl hne
    · simp only [hc, hd, ↓reduceIte] at hne ⊢
      split_ifs at hne ⊢ with hcond
      · exact ⟨_, _, rfl, dDp_lt R, pmul_lt _ _, Or.inl ⟨hcond.1, rfl, rfl, Or.inl ⟨rfl, hcond.2⟩⟩⟩
      · exact absurd rfl hne
  · by_cases hd : dir = 1
    · simp only [hc, hd, ↓reduceIte] at hne ⊢
      split_ifs at hne ⊢ with hcond
      · exact ⟨_, _, rfl, dD_lt R, pmul_lt _ _,
          Or.inr ⟨hcond.1, rfl, rfl, Or.inr ⟨hc, hcond.2.1, hcond.2.2⟩⟩⟩
      · exact absurd rfl hne
    · simp only [hc, hd, ↓reduceIte] at hne ⊢
      split_ifs at hne ⊢ with hcond
      · exact ⟨_, _, rfl, dDp_lt R, pmul_lt _ _,
          Or.inl ⟨hcond.1, rfl, rfl, Or.inr ⟨hc, hcond.2.1, hcond.2.2⟩⟩⟩
      · exact absurd rfl hne

theorem wStep_spec {blk LT PBT : ℕ → ℕ} {NL TL NB BB i Ri ft fd J c D P ri o : ℕ}
    (hD : D < 2 ^ 14) (hP : P < 2 ^ 64) (hr : ri < 2 ^ 8)
    (hne : wStep blk LT PBT NL TL NB BB i Ri ft fd J c (mkW D P ri o) ≠ 0) :
    (¬(c = 255 ∨ c = TL) → c < NL ∧ ltN (LT c) = true ∧
      wStep blk LT PBT NL TL NB BB i Ri ft fd J c (mkW D P ri o) =
        mkW D (pmul P (Nat.land (LT c) m64)) ri o) ∧
    ((c = 255 ∨ c = TL) → ri = ft → ∃ D' P',
      wStep blk LT PBT NL TL NB BB i Ri ft fd J c (mkW D P ri o) = mkW D' P' (ri + 1) 1 ∧
        D' < 2 ^ 14 ∧ P' < 2 ^ 64 ∧ RStep PBT NB BB c Ri D P D' P') ∧
    ((c = 255 ∨ c = TL) → ri ≠ ft → ∃ h < i, ∃ D' P',
      wStep blk LT PBT NL TL NB BB i Ri ft fd J c (mkW D P ri o) = mkW D' P' (ri + 1) o ∧
        D' < 2 ^ 14 ∧ P' < 2 ^ 64 ∧ RStep PBT NB BB c (fct blk h) D P D' P') := by
  obtain ⟨eD, eP, eR, eO⟩ := mkW_dec (own := o) hD hP hr
  have key : wStep blk LT PBT NL TL NB BB i Ri ft fd J c (mkW D P ri o) =
      if c = 255 ∨ c = TL then
        (if ri = ft then refApply PBT NB BB c Ri fd 1 (mkW D P ri o) else
          (if Nat.land (Nat.shiftRight J (Nat.mul 32 (Nat.sub ri o))) m32 >>> 1 < i then
            refApply PBT NB BB c (fct blk (Nat.land (Nat.shiftRight J (Nat.mul 32 (Nat.sub ri o)))
              m32 >>> 1)) (Nat.land (Nat.land (Nat.shiftRight J (Nat.mul 32 (Nat.sub ri o))) m32) 1)
              o (mkW D P ri o) else 0))
      else
        (if c < NL ∧ ltN (LT c) = true then mkW D (pmul P (Nat.land (LT c) m64)) ri o else 0) := by
    unfold wStep
    rw [eD, eP, eR, eO]
    simp only [strictN_eq, brec_eq, orB_iff, andB_iff, Nat.beq_eq, Nat.blt_eq]
    rfl
  rw [key] at hne
  refine ⟨fun hc => ?_, fun hc hft => ?_, fun hc hft => ?_⟩
  · rw [key, ite_eq_right hc]
    rw [ite_eq_right hc] at hne
    split_ifs at hne ⊢ with hcond
    · exact ⟨hcond.1, hcond.2, rfl⟩
    · exact absurd rfl hne
  · rw [key, ite_eq_left hc, ite_eq_left hft]
    rw [ite_eq_left hc, ite_eq_left hft] at hne
    exact refApply_spec hD hP hr hne
  · rw [key, ite_eq_left hc, ite_eq_right hft]
    rw [ite_eq_left hc, ite_eq_right hft] at hne
    split_ifs at hne ⊢ with hlt
    · obtain ⟨D', P', e, h1, h2, h3⟩ := refApply_spec hD hP hr hne
      exact ⟨_, hlt, D', P', e, h1, h2, h3⟩
    · exact absurd rfl hne

theorem walkRun_succ (blk LT PBT : ℕ → ℕ) (NL TL NB BB i Ri ft fd J W n k st : ℕ) :
    walkRun blk LT PBT NL TL NB BB i Ri ft fd J W n (k + 1) st =
      strictN (wStep blk LT PBT NL TL NB BB i Ri ft fd J (wLet W (Nat.sub n (Nat.succ k))) st)
        (fun s => Bool.rec (motive := fun _ => ℕ)
          (walkRun blk LT PBT NL TL NB BB i Ri ft fd J W n k s) 0 (Nat.beq s 0)) := rfl

noncomputable def wSeq (blk LT PBT : ℕ → ℕ) (NL TL NB BB i Ri ft fd J W st0 : ℕ) : ℕ → ℕ
  | 0 => st0
  | q + 1 => wStep blk LT PBT NL TL NB BB i Ri ft fd J (wLet W q)
      (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 q)

theorem walkRun_wSeq (blk LT PBT : ℕ → ℕ) (NL TL NB BB i Ri ft fd J W n st0 : ℕ) :
    ∀ k q, q + k = n →
    walkRun blk LT PBT NL TL NB BB i Ri ft fd J W n k
      (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 q) ≠ 0 →
    (∀ q', q ≤ q' → q' < n → wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 (q' + 1) ≠ 0) ∧
      walkRun blk LT PBT NL TL NB BB i Ri ft fd J W n k
        (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 q) =
        wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 n
  | 0, q, hq, _ => by
    rw [Nat.add_zero] at hq
    subst hq
    exact ⟨fun q' h1 h2 => absurd h2 (by omega), rfl⟩
  | k + 1, q, hq, hne => by
    rw [walkRun_succ, strictN_eq] at hne ⊢
    have e : Nat.sub n (Nat.succ k) = q := by
      change n - (k + 1) = q
      omega
    rw [e] at hne ⊢
    have e2 : wStep blk LT PBT NL TL NB BB i Ri ft fd J (wLet W q)
        (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 q) =
        wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 (q + 1) := rfl
    rw [e2] at hne ⊢
    by_cases h0 : wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 (q + 1) = 0
    · rw [h0] at hne
      exact absurd rfl hne
    · have hb : Nat.beq (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 (q + 1)) 0 = false := by
        cases e3 : Nat.beq (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W st0 (q + 1)) 0
        · rfl
        · rw [Nat.beq_eq] at e3
          exact absurd e3 h0
      rw [hb] at hne ⊢
      obtain ⟨h1, h2⟩ := walkRun_wSeq blk LT PBT NL TL NB BB i Ri ft fd J W n st0 k (q + 1)
        (by omega) hne
      refine ⟨fun q' hq1 hq2 => ?_, h2⟩
      rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
      · exact h0
      · exact h1 q' hq1 hq2

@[expose] def OwnAt (TL W ft q : ℕ) : Prop :=
  (wLet W q = 255 ∨ wLet W q = TL) ∧ refCount TL W q = ft

theorem ownAt_unique {TL W ft q q' : ℕ} (h : OwnAt TL W ft q) (h' : OwnAt TL W ft q') : q = q' := by
  have key : ∀ a b, a < b → OwnAt TL W ft a → OwnAt TL W ft b → False := by
    intro a b hab ha hb
    have h1 := refCount_mono TL W (Nat.succ_le_of_lt hab)
    rw [refCount_succ, ite_eq_left ha.1] at h1
    have h2 := ha.2
    have h3 := hb.2
    omega
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · exact key _ _ hl h h'
  · exact key _ _ hl h' h

theorem wSeq_inv {blk LT PBT : ℕ → ℕ} {NL TL NB BB i Ri ft fd J W n D0 P0 : ℕ} (hn : n < 256)
    (hD0 : D0 < 2 ^ 14) (hP0 : P0 < 2 ^ 64)
    (hnz : ∀ q < n, wSeq blk LT PBT NL TL NB BB i Ri ft fd J W (mkW D0 P0 0 0) (q + 1) ≠ 0) :
    ∀ q ≤ n, ∃ D P o, wSeq blk LT PBT NL TL NB BB i Ri ft fd J W (mkW D0 P0 0 0) q =
      mkW D P (refCount TL W q) o ∧ D < 2 ^ 14 ∧ P < 2 ^ 64 ∧
      (o = 1 ↔ ∃ q' < q, OwnAt TL W ft q') ∧ (o = 0 ∨ o = 1)
  | 0, _ => ⟨D0, P0, 0, rfl, hD0, hP0, by simp, Or.inl rfl⟩
  | q + 1, hq => by
    obtain ⟨D, P, o, e, hD, hP, ho, ho01⟩ := wSeq_inv hn hD0 hP0 hnz q (by omega)
    have hri : refCount TL W q < 2 ^ 8 := Nat.lt_of_le_of_lt (refCount_le TL W q) (by omega)
    have hne := hnz q (by omega)
    have e1 : wSeq blk LT PBT NL TL NB BB i Ri ft fd J W (mkW D0 P0 0 0) (q + 1) =
        wStep blk LT PBT NL TL NB BB i Ri ft fd J (wLet W q) (mkW D P (refCount TL W q) o) := by
      change wStep _ _ _ _ _ _ _ _ _ _ _ _ _ (wSeq blk LT PBT NL TL NB BB i Ri ft fd J W
        (mkW D0 P0 0 0) q) = _
      rw [e]
    rw [e1] at hne ⊢
    obtain ⟨hN, hOwn, hRef⟩ := wStep_spec hD hP hri hne
    have hsplit : (∃ q' < q + 1, OwnAt TL W ft q') ↔
        (∃ q' < q, OwnAt TL W ft q') ∨ OwnAt TL W ft q :=
      ⟨fun ⟨q', h1, h2⟩ => (Nat.lt_succ_iff_lt_or_eq.mp h1).elim (fun h => Or.inl ⟨q', h, h2⟩)
        (fun h => Or.inr (h ▸ h2)),
       fun h => h.elim (fun ⟨q', h1, h2⟩ => ⟨q', by omega, h2⟩) (fun h => ⟨q, by omega, h⟩)⟩
    by_cases hc : wLet W q = 255 ∨ wLet W q = TL
    · have hrc : refCount TL W (q + 1) = refCount TL W q + 1 := by
        rw [refCount_succ, ite_eq_left hc]
      by_cases hft : refCount TL W q = ft
      · obtain ⟨D', P', e2, hD', hP', -⟩ := hOwn hc hft
        refine ⟨D', P', 1, by rw [e2, hrc], hD', hP', ?_, Or.inr rfl⟩
        rw [hsplit]
        exact ⟨fun _ => Or.inr ⟨hc, hft⟩, fun _ => rfl⟩
      · obtain ⟨h, -, D', P', e2, hD', hP', -⟩ := hRef hc hft
        refine ⟨D', P', o, by rw [e2, hrc], hD', hP', ?_, ho01⟩
        rw [hsplit, ho]
        exact ⟨Or.inl, fun h' => h'.elim id (fun h'' => absurd h''.2 hft)⟩
    · have hrc : refCount TL W (q + 1) = refCount TL W q := by
        rw [refCount_succ, ite_eq_right hc]
      obtain ⟨-, -, e2⟩ := hN hc
      refine ⟨D, _, o, by rw [e2, hrc], hD, pmul_lt _ _, ?_, ho01⟩
      rw [hsplit, ho]
      exact ⟨Or.inl, fun h' => h'.elim id (fun h'' => absurd h''.1 hc)⟩

@[expose] def WalkOn (blk LT PBT : ℕ → ℕ) (NL TL NB BB i R W n D0 P0 : ℕ) : Prop :=
  ∃ Ds Ps : ℕ → ℕ, ∃ qo < n, Ds 0 = D0 ∧ Ps 0 = P0 ∧ Ds n = D0 ∧ Ps n = P0 ∧
    (wLet W qo = 255 ∨ wLet W qo = TL) ∧ ∀ q < n,
      (wLet W q ≠ 255 → wLet W q ≠ TL → wLet W q < NL ∧ ltN (LT (wLet W q)) = true ∧
        Ds (q + 1) = Ds q ∧ Ps (q + 1) = pmul (Ps q) (Nat.land (LT (wLet W q)) m64)) ∧
      (q = qo → RStep PBT NB BB (wLet W q) R (Ds q) (Ps q) (Ds (q + 1)) (Ps (q + 1))) ∧
      (q ≠ qo → (wLet W q = 255 ∨ wLet W q = TL) → ∃ h < i,
        RStep PBT NB BB (wLet W q) (fct blk h) (Ds q) (Ps q) (Ds (q + 1)) (Ps (q + 1)))

theorem walkOK_spec {blk LT HT PBT : ℕ → ℕ} {NL TL NB BB NH ND i R J w : ℕ} (hND : ND ≤ 16384)
    (h : walkOK blk LT HT PBT NL TL NB BB NH ND i R J w = true) :
    ∃ a < NH, ∃ b < NH, ∃ D0 < ND,
      WalkOn blk LT PBT NL TL NB BB i R (wW w) (wN w) D0 (hQuot HT a b) := by
  unfold walkOK at h
  simp only [andB_iff, Nat.blt_eq, letB_eq, Nat.beq_eq] at h
  obtain ⟨ha, hb, hd, hw⟩ := h
  refine ⟨_, ha, _, hb, _, hd, ?_⟩
  have hP0 : hQuot HT (Nat.land (Nat.shiftRight J 10) 65535)
      (Nat.land (Nat.shiftRight J 26) 65535) < 2 ^ 64 := pmul_lt _ _
  generalize Nat.land (Nat.shiftRight J 42) 65535 = D0 at hd hw ⊢
  generalize hQuot HT (Nat.land (Nat.shiftRight J 10) 65535)
    (Nat.land (Nat.shiftRight J 26) 65535) = P0 at hw hP0 ⊢
  generalize Nat.land (Nat.shiftRight J 58) 255 = ft at hw
  generalize Nat.land (Nat.shiftRight J 66) 1 = fd at hw
  generalize Nat.shiftRight J 67 = Jr at hw
  have hn : wN w < 256 := Nat.and_lt_two_pow w (n := 8) (by norm_num)
  have hnr : wNr w < 2 ^ 8 := Nat.and_lt_two_pow _ (n := 8) (by norm_num)
  generalize wN w = n at hn hw ⊢
  generalize wW w = W at hw ⊢
  have hD0 : D0 < 2 ^ 14 := by omega
  have h00 : (0 : ℕ) < 2 ^ 8 := by norm_num
  have hfin : mkW D0 P0 (wNr w) 1 ≠ 0 := fun h0 => by
    have := (mkW_dec (own := 1) hD0 hP0 hnr).2.2.2
    rw [h0] at this
    exact absurd this (by decide)
  obtain ⟨hnz, hend⟩ := walkRun_wSeq blk LT PBT NL TL NB BB i R ft fd Jr W n (mkW D0 P0 0 0) n 0
    (by omega) (fun h0 => hfin (hw.symm.trans h0))
  have hnz' : ∀ q < n, wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) (q + 1) ≠ 0 :=
    fun q hq => hnz q (Nat.zero_le _) hq
  have inv := wSeq_inv hn hD0 hP0 hnz'
  have hstep : ∀ q, wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) (q + 1) =
      wStep blk LT PBT NL TL NB BB i R ft fd Jr (wLet W q)
        (wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) q) := fun _ => rfl
  have hS0 : wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) 0 = mkW D0 P0 0 0 := rfl
  have hSn : wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) n = mkW D0 P0 (wNr w) 1 :=
    hend.symm.trans hw
  clear hnz hend
  generalize wSeq blk LT PBT NL TL NB BB i R ft fd Jr W (mkW D0 P0 0 0) = S
    at hnz' inv hstep hS0 hSn
  have dec : ∀ q D P r o, D < 2 ^ 14 → P < 2 ^ 64 → r < 2 ^ 8 → S q = mkW D P r o →
      DceS.sD (S q) = D ∧ DceS.sP (S q) = P := fun q D P r o hD hP hr e => by
    rw [e]
    exact ⟨(mkW_dec hD hP hr).1, (mkW_dec hD hP hr).2.1⟩
  obtain ⟨Dn, Pn, on, en, hDn, hPn, hon, -⟩ := inv n le_rfl
  have hrn : refCount TL W n < 2 ^ 8 := Nat.lt_of_le_of_lt (refCount_le TL W n) (by omega)
  have e1 := mkW_dec (own := on) hDn hPn hrn
  have e2 := mkW_dec (own := 1) hD0 hP0 hnr
  rw [← en, hSn] at e1
  have hDn0 : Dn = D0 := e1.1.symm.trans e2.1
  have hPn0 : Pn = P0 := e1.2.1.symm.trans e2.2.1
  have hon1 : on = 1 := e1.2.2.2.symm.trans e2.2.2.2
  obtain ⟨qo, hqo, hown⟩ := hon.1 hon1
  refine ⟨fun q => DceS.sD (S q), fun q => DceS.sP (S q), qo, hqo, ?_, ?_, ?_, ?_, hown.1,
    fun q hq => ?_⟩
  · dsimp only
    rw [hS0]
    exact (mkW_dec hD0 hP0 h00).1
  · dsimp only
    rw [hS0]
    exact (mkW_dec hD0 hP0 h00).2.1
  · dsimp only
    rw [(dec n _ _ _ _ hDn hPn hrn en).1, hDn0]
  · dsimp only
    rw [(dec n _ _ _ _ hDn hPn hrn en).2, hPn0]
  obtain ⟨D, P, o, eq, hD, hP, -, -⟩ := inv q (le_of_lt hq)
  have hri : refCount TL W q < 2 ^ 8 := Nat.lt_of_le_of_lt (refCount_le TL W q) (by omega)
  have hri1 : refCount TL W q + 1 < 2 ^ 8 :=
    Nat.lt_of_le_of_lt (Nat.succ_le_succ (refCount_le TL W q)) (by omega)
  have eS : S (q + 1) = wStep blk LT PBT NL TL NB BB i R ft fd Jr (wLet W q)
      (mkW D P (refCount TL W q) o) := by
    rw [hstep, eq]
  have hne : wStep blk LT PBT NL TL NB BB i R ft fd Jr (wLet W q)
      (mkW D P (refCount TL W q) o) ≠ 0 := eS ▸ hnz' q hq
  obtain ⟨hN, hOwn, hRef⟩ := wStep_spec hD hP hri hne
  obtain ⟨hDq, hPq⟩ := dec q _ _ _ _ hD hP hri eq
  dsimp only
  rw [hDq, hPq]
  refine ⟨fun h1 h2 => ?_, fun hq0 => ?_, fun hq0 hc => ?_⟩
  · have hc : ¬(wLet W q = 255 ∨ wLet W q = TL) := fun h' => h'.elim h1 h2
    obtain ⟨hl, hlN, e3⟩ := hN hc
    obtain ⟨h3, h4⟩ := dec (q + 1) _ _ _ _ hD (pmul_lt _ _) hri (eS.trans e3)
    exact ⟨hl, hlN, h3, h4⟩
  · subst hq0
    obtain ⟨D', P', e3, hD', hP', hR⟩ := hOwn hown.1 hown.2
    obtain ⟨h3, h4⟩ := dec (q + 1) _ _ _ _ hD' hP' hri1 (eS.trans e3)
    rw [h3, h4]
    exact hR
  · have hft : refCount TL W q ≠ ft := fun e' => hq0 (ownAt_unique ⟨hc, e'⟩ hown)
    obtain ⟨h', hh', D', P', e3, hD', hP', hR⟩ := hRef hc hft
    obtain ⟨h3, h4⟩ := dec (q + 1) _ _ _ _ hD' hP' hri1 (eS.trans e3)
    rw [h3, h4]
    exact ⟨h', hh', hR⟩

@[expose] def TreeF (R nx : ℕ) : Prop := 0 < dJ R ∧ dDp R = nx ∧ dD R < nx ∧ dP R = idP

@[expose] def AxF (HT : ℕ → ℕ) (NH R : ℕ) : Prop :=
  dD R = 0 ∧ dJ R = 0 ∧ dDp R = 0 ∧ ∃ a < NH, ∃ b < NH, dP R = hQuot HT a b

@[expose] def FactRaw (blk LT HT PBT WT : ℕ → ℕ) (NL TL NB BB NH ND NO i nx nx' : ℕ) : Prop :=
  DceS.recOK ND NO (fct blk i) = true ∧
    (nx' = nx + 1 ∧ TreeF (fct blk i) nx ∨ nx' = nx ∧ AxF HT NH (fct blk i) ∨
      nx' = nx ∧ ∃ J, walkOK blk LT HT PBT NL TL NB BB NH ND i (fct blk i) J
        (WT (Nat.land (Nat.shiftRight J 2) 255)) = true)

@[expose] def FInv (blk LT HT PBT WT : ℕ → ℕ) (NL TL NB BB NH ND NO S : ℕ) : Prop :=
  S = 0 ∨ ∃ i nx, S = mkS i nx ∧ i < 2 ^ 32 ∧ ∃ nxf : ℕ → ℕ, 1 ≤ nxf 0 ∧ nxf i = nx ∧
    ∀ i' < i, FactRaw blk LT HT PBT WT NL TL NB BB NH ND NO i' (nxf i') (nxf (i' + 1))

theorem factStep_inv {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO J S : ℕ}
    (h : FInv blk LT HT PBT WT NL TL NB BB NH ND NO S) :
    FInv blk LT HT PBT WT NL TL NB BB NH ND NO
      (factStep blk LT HT PBT NL TL NB BB NH ND NO J S (fct blk (sI S))
        (WT (Nat.land (Nat.shiftRight J 2) 255))) := by
  rcases h with rfl | ⟨i, nx, rfl, hi, nxf, h0, hnx, hf⟩
  · exact Or.inl rfl
  obtain ⟨eI, eN⟩ := mkS_dec nx hi
  by_cases hz : factStep blk LT HT PBT NL TL NB BB NH ND NO J (mkS i nx) (fct blk (sI (mkS i nx)))
      (WT (Nat.land (Nat.shiftRight J 2) 255)) = 0
  · exact Or.inl hz
  have key : ∃ nx', factStep blk LT HT PBT NL TL NB BB NH ND NO J (mkS i nx)
      (fct blk (sI (mkS i nx))) (WT (Nat.land (Nat.shiftRight J 2) 255)) = mkS (i + 1) nx' ∧
      FactRaw blk LT HT PBT WT NL TL NB BB NH ND NO i nx nx' := by
    unfold factStep at hz ⊢
    rw [eI, eN] at hz ⊢
    simp only [brec_eq, andB_iff, Nat.blt_eq, Nat.beq_eq] at hz ⊢
    split_ifs at hz ⊢ with c1 c2 c3 c4 c5 c6 c7
    all_goals first | exact absurd rfl hz | skip
    · exact ⟨_, rfl, c2, Or.inl ⟨rfl, c4⟩⟩
    · obtain ⟨hl, ha, hb, hp⟩ := c6
      obtain ⟨d1, d2, d3⟩ := low39 hl
      exact ⟨_, rfl, c2, Or.inr (Or.inl ⟨rfl, d1, d2, d3, _, ha, _, hb, hp⟩)⟩
    · exact ⟨_, rfl, c2, Or.inr (Or.inr ⟨rfl, J, c7.2⟩)⟩
  obtain ⟨nx', e, hfr⟩ := key
  rw [eI] at e
  rw [eI, e]
  rcases Nat.lt_or_ge (i + 1) (2 ^ 32) with hlt | hge
  · refine Or.inr ⟨i + 1, nx', rfl, hlt, fun i' => if i' ≤ i then nxf i' else nx', ?_, ?_, ?_⟩
    · simpa using h0
    · simp
    · intro i' hi'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · have h1 : i' ≤ i := by omega
        have h2 : i' + 1 ≤ i := by omega
        simp only [h1, h2, ↓reduceIte]
        exact hf i' hi'
      · simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
        rw [hnx]
        exact hfr
  · have e2 : i + 1 = 2 ^ 32 := by omega
    rw [e2, mkS_wrap]
    exact Or.inr ⟨0, _, rfl, by norm_num, fun _ => Nat.lor 1 nx', one_le_lor nx', rfl,
      fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

theorem rec_inv {P : ℕ → Prop} (s : ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ)
    (hs : ∀ k (ih : ℕ → ℕ → ℕ), (∀ J S, P S → P (ih J S)) → ∀ J S, P S → P (s k ih J S)) :
    ∀ k J S, P S → P (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S) s k J S)
  | 0, _, _, h => h
  | k + 1, J, S, h => hs k _ (rec_inv s hs k) J S h

theorem runChunk_inv {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO C S : ℕ}
    (h : FInv blk LT HT PBT WT NL TL NB BB NH ND NO S) :
    FInv blk LT HT PBT WT NL TL NB BB NH ND NO
      (runChunk blk LT HT PBT WT NL TL NB BB NH ND NO C S) := by
  unfold runChunk
  exact rec_inv _ (fun _ _ hih J S hS => by
    simp only [strictN_eq]
    exact hih _ _ (factStep_inv hS)) _ _ _ h

theorem runFacts_inv {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO : ℕ} :
    ∀ (Cs : List ℕ) (S : ℕ), FInv blk LT HT PBT WT NL TL NB BB NH ND NO S →
      FInv blk LT HT PBT WT NL TL NB BB NH ND NO
        (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change FInv blk LT HT PBT WT NL TL NB BB NH ND NO
      (strictN (runChunk blk LT HT PBT WT NL TL NB BB NH ND NO C S)
        (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs))
    rw [strictN_eq]
    exact runFacts_inv Cs _ (runChunk_inv h)

@[expose] def WalkSem (blk LT HT PBT WT : ℕ → ℕ) (NL TL NB BB NH ND NW i : ℕ) : Prop :=
  ∃ t < NW, ∃ a < NH, ∃ b < NH, ∃ D0 < ND,
    WalkOn blk LT PBT NL TL NB BB i (fct blk i) (wW (WT t)) (wN (WT t)) D0 (hQuot HT a b)

@[expose] def FactSem (blk LT HT PBT WT : ℕ → ℕ) (NL TL NB BB NH ND NO NW i nx nx' : ℕ) : Prop :=
  DceS.recOK ND NO (fct blk i) = true ∧
    (nx' = nx + 1 ∧ TreeF (fct blk i) nx ∨ nx' = nx ∧ AxF HT NH (fct blk i) ∨
      nx' = nx ∧ WalkSem blk LT HT PBT WT NL TL NB BB NH ND NW i)

theorem wtDceOK_spec {WT : ℕ → ℕ} {m P : ℕ} (h : wtDceOK WT m P = true) :
    ∀ k < 256, WT k = 0 ∨ (k % P < m ∧ WT k = WT (k % P)) := by
  intro k hk
  unfold wtDceOK at h
  have := (allRec2_iff (fun k => orB (Nat.beq (WT k) (nat_lit 0))
    (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))))) 256).1 h k hk
  simp only [orB_iff, andB_iff, Nat.beq_eq, Nat.blt_eq] at this
  exact this

theorem facts_sound {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO NW P nf S0 S1 : ℕ}
    {Cs : List ℕ} (hrun : runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs S0 = S1)
    (hS0 : S0 = mkS 0 1) (hS1 : S1 = mkS nf ND) (hnf : nf < 2 ^ 32) (hND : 0 < ND)
    (hND' : ND ≤ 16384) (hwt : wtDceOK WT NW P = true) :
    ∃ nxf : ℕ → ℕ, 1 ≤ nxf 0 ∧ nxf nf = ND ∧
      ∀ i < nf, FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i (nxf i) (nxf (i + 1)) := by
  have h0 : FInv blk LT HT PBT WT NL TL NB BB NH ND NO S0 :=
    Or.inr ⟨0, 1, hS0, by norm_num, fun _ => 1, le_rfl, rfl, fun i' hi' => absurd hi' (by omega)⟩
  have h1 := runFacts_inv Cs S0 h0
  rw [hrun, hS1] at h1
  rcases h1 with h1 | ⟨i, nx, e, hi, nxf, hnxf0, hnx, hf⟩
  · rw [mkS_eq ND hnf] at h1
    have : 0 < ND * 2 ^ 32 := Nat.mul_pos hND (by positivity)
    omega
  obtain ⟨d1, d2⟩ := mkS_dec ND hnf
  obtain ⟨d3, d4⟩ := mkS_dec nx hi
  rw [e] at d1 d2
  rw [d1] at d3
  rw [d2] at d4
  subst d3
  subst d4
  refine ⟨nxf, hnxf0, hnx, fun i' hi' => ?_⟩
  obtain ⟨hrec, ht | ha | ⟨hw, J, hJ⟩⟩ := hf i' hi'
  · exact ⟨hrec, Or.inl ht⟩
  · exact ⟨hrec, Or.inr (Or.inl ha)⟩
  · refine ⟨hrec, Or.inr (Or.inr ⟨hw, ?_⟩)⟩
    obtain ⟨a, ha, b, hb, D0, hD0, hwalk⟩ := walkOK_spec hND' hJ
    have hk : Nat.land (Nat.shiftRight J 2) 255 < 256 :=
      Nat.and_lt_two_pow _ (n := 8) (by norm_num)
    rcases wtDceOK_spec hwt _ hk with h0 | ⟨hlt, heq⟩
    · rw [h0] at hwalk
      obtain ⟨-, -, qo, hqo, -⟩ := hwalk
      exact absurd hqo (Nat.not_lt_zero _)
    · rw [heq] at hwalk
      exact ⟨_, hlt, a, ha, b, hb, D0, hD0, hwalk⟩

theorem FactSem_mono {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO NW i nx nx' : ℕ}
    (h : FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i nx nx') : nx ≤ nx' := by
  rcases h.2 with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> omega

theorem FactSem_tree {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO NW i nx : ℕ}
    (h : FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i nx (nx + 1)) :
    TreeF (fct blk i) nx := by
  rcases h.2 with ⟨-, ht⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact ht
  · omega
  · omega

theorem tree_unique {blk LT HT PBT WT : ℕ → ℕ} {NL TL NB BB NH ND NO NW nf : ℕ} {nxf : ℕ → ℕ}
    (hf : ∀ i < nf, FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i (nxf i) (nxf (i + 1)))
    {i i' : ℕ} (hi : i < nf) (hi' : i' < nf) (ht : nxf (i + 1) = nxf i + 1)
    (ht' : nxf (i' + 1) = nxf i' + 1) (e : dDp (fct blk i) = dDp (fct blk i')) : i = i' := by
  have mono : ∀ a b, a ≤ b → b ≤ nf → nxf a ≤ nxf b := by
    intro a b hab hb
    induction b with
    | zero =>
      rw [Nat.le_zero.1 hab]
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hab) with h1 | h1
      · exact Nat.le_trans (ih (by omega) (by omega)) (FactSem_mono (hf k (by omega)))
      · rw [h1]
  have t1 := FactSem_tree (ht ▸ hf i hi)
  have t2 := FactSem_tree (ht' ▸ hf i' hi')
  rw [t1.2.1, t2.2.1] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := mono (i + 1) i' (by omega) (by omega)
    omega
  · have := mono (i' + 1) i (by omega) (by omega)
    omega

section DceOk

variable {blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : ℕ → ℕ}
  {NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
    hL hH hO hR hD P : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}

theorem dceOk_spec (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) :
    constOK OMT NB NO I0 BB BASEM NL TL ND ALIVE = true ∧ invSelfOK INV INV8 NL = true ∧
    invRelOK RT NL NR IH = true ∧ allBelow NL hL (letOK LT TL) = true ∧
    allBelow NH hH (hdrOK HT LT NL) = true ∧
    allBelow NO hO (omOK PBT OMT GT HT NB NH (PBT I0)) = true ∧
    wordsOK WT RT LT INV INV8 NL TL NR NW HS = true ∧ allBelow NR hR (relOK RT LT NL TL) = true ∧
    wtDceOK WT NW P = true ∧ Nat.ble NL (Nat.mul 64 hL) = true ∧ Nat.ble NH (Nat.mul 64 hH) = true ∧
    Nat.ble NO (Nat.mul 64 hO) = true ∧ Nat.ble NR (Nat.mul 64 hR) = true ∧
    Nat.ble ND (Nat.mul 64 hD) = true ∧ Nat.ble ND 16384 = true ∧ Nat.blt NH 65536 = true ∧
    Nat.blt nf 4294967296 = true ∧ Nat.blt nN 16777215 = true ∧ Nat.beq S0 (mkS 0 1) = true ∧
    Nat.beq (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs S0) S1 = true ∧
    Nat.beq S1 (mkS nf ND) = true ∧ Nat.beq X0 1 = true ∧
    Nat.beq (runCover blk PBT OMT NB NO hO ALIVE nf CCs X0) X1 = true ∧
    Nat.beq X1 (Nat.succ ND) = true ∧ Nat.beq ngN (Nat.sub NL 1) = true ∧
    Nat.beq (eCnt (enumRun NE (nGens LT NL TL) ngN nN 0 nN 1)) (Nat.succ nN) = true ∧
    Nat.blt SUMIDX failV = true ∧ Nat.beq (indexSum blk SE STT nf nN ND hD ALIVE) SUMIDX = true ∧
    Nat.ble ngT 7 = true ∧ tgOK PBT OMT NB I0 TGs ngT = true ∧
    Nat.beq (eCnt (enumRun TTE TGs ngT nT 0 nT 1)) (Nat.succ nT) = true ∧
    Nat.beq (Nat.mul nT NO) nN = true ∧
    allBelow NO hO (CFSG.KC.Co1M.omClosOK LT PBT OMT OHT NL TL NB NO) = true := by
  unfold dceOk at h
  simp only [andB_iff] at h
  exact h

theorem dceOk_letters (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) :
    TL < NL ∧ NL < 255 ∧ (∀ c < NL, letOK LT TL c = true) ∧
      ∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
        pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP := by
  obtain ⟨h1, h2, h3, h4, -, -, -, h8, -, h10, -, -, h13, -⟩ := dceOk_spec h
  have hTL := (constOK_spec h1).2.2.2.2.1
  have hNL := (invSelfOK_spec h2).1
  have hl := allBelow_spec h4 (by simpa using h10)
  have hr := allBelow_spec h8 (by simpa using h13)
  exact ⟨hTL, hNL, hl, fun c hc hcT =>
    ⟨((letOK_spec (hl c hc)).2 hcT).2, L_invol h3 hNL hr hl c hc hcT⟩⟩

theorem dceOk_hdr (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) :
    ∀ k < NH, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = hP (HT k) := by
  obtain ⟨-, -, -, -, h5, -, -, -, -, -, h11, -⟩ := dceOk_spec h
  exact hdr_word (allBelow_spec h5 (by simpa using h11)) (dceOk_letters h).2.2.1

theorem dceOk_hdr_isP (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) : ∀ k < NH, IsP (hP (HT k)) := by
  intro k hk
  obtain ⟨w, hw, e⟩ := dceOk_hdr h k hk
  rw [← e]
  exact (wc_spec fun c hc => ((dceOk_letters h).2.2.2 c (hw c hc).1 (hw c hc).2).1).1

theorem dceOk_omega (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) :
    I0 < NO ∧ bbOK NB BB (OMT I0) = true ∧
    (∀ j < NO, sysPB NB (PBT j) = sysOf NB (OMT j) ∧ (sysOf NB (OMT j)).card = NB) ∧
    (∀ i < NO, ∀ i' < NO, sysOf NB (OMT i) = sysOf NB (OMT i') → i = i') ∧
    (∀ j < NO, GT j < NH ∧
      (perm16 (hP (HT (GT j))))⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT j)) ∧
    (∀ j < NO, ∀ c < NL, c ≠ TL → ∃ h' < NO,
      (perm16 (Nat.land (LT c) m64))⁻¹ • sysOf NB (OMT j) = sysOf NB (OMT h')) ∧
    (∀ k < ngT, IsP (gk TGs k) ∧
      (perm16 (gk TGs k))⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT I0)) := by
  obtain ⟨h1, -, -, -, -, h6, -, -, -, -, -, h12, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, h30, -, -, h33⟩ := dceOk_spec h
  obtain ⟨-, hNB, hI0, hbb, hTL, -⟩ := constOK_spec h1
  have hO := allBelow_spec h6 (by simpa using h12)
  have hC := allBelow_spec h33 (by simpa using h12)
  have hsys : ∀ j < NO, sysPB NB (PBT j) = sysOf NB (OMT j) ∧ (sysOf NB (OMT j)).card = NB :=
    fun j hj => omOK_sys (hO j hj)
  refine ⟨hI0, hbb, hsys, omOK_inj hNB hO, fun j hj => ?_, fun j hj c hc hcT => ?_,
    fun k hk => ?_⟩
  · have hg := (omOK_parts (hO j hj)).2.2.2.2.1
    exact omOK_g (hO j hj) (hO I0 hI0) (dceOk_hdr_isP h _ hg)
  · obtain ⟨h', hh', hm⟩ := omClosOK_spec (hC j hj) hTL c hc hcT
    exact ⟨h', hh', sys_img ((dceOk_letters h).2.2.2 c hc hcT).1 (hsys j hj).1 (hsys j hj).2
      (hsys h' hh').2 hm⟩
  · obtain ⟨hp, hm⟩ := tgOK_spec h30 k hk
    exact ⟨hp, sys_img hp (hsys I0 hI0).1 (hsys I0 hI0).2 (hsys I0 hI0).2 hm⟩

theorem dceOk_tstep (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) {Q j : ℕ} (hQ : IsP Q) (hj : j < NO)
    (ha : allIn NB BB (imgMasks Q (PBT j)) = true) :
    (perm16 Q)⁻¹ • sysOf NB (OMT j) = sysOf NB (OMT I0) := by
  obtain ⟨hI0, hbb, hsys, -⟩ := dceOk_omega h
  exact allIn_sys hbb hQ (hsys j hj).1 (hsys j hj).2 (hsys I0 hI0).2 ha

theorem dceOk_words {G : Type*} [Group G] (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB
      NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR
      hD P Cs CCs S0 S1 X0 X1 = true) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1) :
    (∀ c < NL, x c * x c = 1) ∧ ∀ t < NW,
      lettersD LT NL TL (wW (WT t)) (wN (WT t)) = true ∧
      refCount TL (wW (WT t)) (wN (WT t)) = wNr (WT t) ∧
      bvF (fun c => if c = 255 then 1 else x c) (wW (WT t)) (wN (WT t)) = 1 := by
  obtain ⟨-, h2, h3, -, -, -, h7, h8, -, -, -, -, h13, -⟩ := dceOk_spec h
  have hNL := (invSelfOK_spec h2).1
  have hr := allBelow_spec h8 (by simpa using h13)
  have hx := x_invol h3 (by omega) x hrels
  refine ⟨hx, wordsOK_sound h2 h7 (fun r hr' => (relOK_spec (hr r hr')).1) _ (by simp)
    (fun c hc => ?_) (fun r hr' => ?_)⟩
  · have hne : c ≠ 255 := by omega
    simp only [hne, ↓reduceIte]
    exact hx c hc
  · rw [rval_eq (hr r hr') hNL x]
    exact hrels r hr'

theorem dceOk_facts (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) :
    ∃ nxf : ℕ → ℕ, 1 ≤ nxf 0 ∧ nxf nf = ND ∧
      ∀ i < nf, FactSem blk LT HT PBT WT NL TL NB BB NH ND NO NW i (nxf i) (nxf (i + 1)) := by
  obtain ⟨h1, -, -, -, -, -, -, -, h9, -, -, -, -, -, h15, -, h17, -, h19, h20, h21, -⟩ :=
    dceOk_spec h
  simp only [Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h15 h17 h19 h20 h21
  exact facts_sound h20 h19 h21 (by simpa using h17) (constOK_spec h1).2.2.2.2.2.2.2 h15 h9

end DceOk

end CFSG.Certificates.Co1D

end
