module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] def spread_V (q u : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => spread_V q u N + u N * 2 ^ (q N)

theorem spread_V_zero (q u : Nat → Nat) : spread_V q u 0 = 0 := rfl

theorem spread_V_succ (q u : Nat → Nat) (N : Nat) :
    spread_V q u (N + 1) = spread_V q u N + u N * 2 ^ (q N) := rfl

theorem spread_V_lt (q u : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8) :
    ∀ N, spread_V q u N < 2 ^ (q N) := by
  intro N
  induction N with
  | zero => exact Nat.two_pow_pos _
  | succ N ih =>
    rw [spread_V_succ]
    have h1 : u N * 2 ^ (q N) ≤ 7 * 2 ^ (q N) := Nat.mul_le_mul_right _ (by have := hu N; omega)
    have h2 : 2 ^ (q N + 3) ≤ 2 ^ (q (N + 1)) := Nat.pow_le_pow_right (by omega) (hq N)
    have h3 : 2 ^ (q N + 3) = 8 * 2 ^ (q N) := by rw [Nat.pow_add]; omega
    omega

theorem spread_and_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) &&& (B + b * 2 ^ w) = (A &&& B) + (a &&& b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A &&& B < 2 ^ w := Nat.and_lt_two_pow _ hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A &&& B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a &&& b), Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_and]

theorem spread_xor_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) ^^^ (B + b * 2 ^ w) = (A ^^^ B) + (a ^^^ b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A ^^^ B < 2 ^ w := Nat.xor_lt_two_pow hA hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A ^^^ B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a ^^^ b), Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_xor]

theorem spread_or_split {A B a b w : Nat} (hA : A < 2 ^ w) (hB : B < 2 ^ w) :
    (A + a * 2 ^ w) ||| (B + b * 2 ^ w) = (A ||| B) + (a ||| b) * 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro n
  have hAB : A ||| B < 2 ^ w := Nat.or_lt_two_pow hA hB
  rw [Nat.add_comm A, Nat.add_comm B, Nat.add_comm (A ||| B), Nat.mul_comm a, Nat.mul_comm b,
    Nat.mul_comm (a ||| b), Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hA,
    Nat.testBit_two_pow_mul_add _ hB, Nat.testBit_two_pow_mul_add _ hAB]
  split <;> simp [Nat.testBit_or]

theorem spread_V_and (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spread_V q u N &&& spread_V q v N = spread_V q (fun j => u j &&& v j) N := by
  induction N with
  | zero => simp [spread_V_zero]
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, spread_V_succ,
      spread_and_split (spread_V_lt q u hq hu N) (spread_V_lt q v hq hv N), ih]

theorem spread_V_xor (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spread_V q u N ^^^ spread_V q v N = spread_V q (fun j => u j ^^^ v j) N := by
  induction N with
  | zero => simp [spread_V_zero]
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, spread_V_succ,
      spread_xor_split (spread_V_lt q u hq hu N) (spread_V_lt q v hq hv N), ih]

theorem spread_V_or (q u v : Nat → Nat) (hq : ∀ j, q j + 3 ≤ q (j + 1)) (hu : ∀ j, u j < 8)
    (hv : ∀ j, v j < 8) (N : Nat) :
    spread_V q u N ||| spread_V q v N = spread_V q (fun j => u j ||| v j) N := by
  induction N with
  | zero => simp [spread_V_zero]
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, spread_V_succ,
      spread_or_split (spread_V_lt q u hq hu N) (spread_V_lt q v hq hv N), ih]

theorem spread_V_shiftLeft (q u : Nat → Nat) (s N : Nat) :
    spread_V q u N <<< s = spread_V (fun j => q j + s) u N := by
  rw [Nat.shiftLeft_eq]
  induction N with
  | zero => simp [spread_V_zero]
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, ← ih, Nat.add_mul, Nat.pow_add, Nat.mul_assoc]

theorem spread_V_congr_pos (q q' u : Nat → Nat) (N : Nat)
    (h : ∀ j < N, u j = 0 ∨ q j = q' j) : spread_V q u N = spread_V q' u N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, ih (fun j hj => h j (by omega))]
    rcases h N (by omega) with h0 | h0 <;> simp [h0]

theorem spread_V_congr_coef (q u v : Nat → Nat) (N : Nat)
    (h : ∀ j < N, u j = v j) : spread_V q u N = spread_V q v N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [spread_V_succ, spread_V_succ, ih (fun j hj => h j (by omega)), h N (by omega)]

@[expose] def spread_P (e j : Nat) : Nat := 3 * j + 10 * (j / 2 ^ e * 2 ^ e)

@[expose] def spread_g (t j : Nat) : Nat := if j / 2 ^ t % 2 = 1 then 7 else 0

theorem spread_P_sep (e : Nat) : ∀ j, spread_P e j + 3 ≤ spread_P e (j + 1) := by
  intro j
  unfold spread_P
  have : j / 2 ^ e * 2 ^ e ≤ (j + 1) / 2 ^ e * 2 ^ e :=
    Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))
  omega

theorem spread_P_step (t j : Nat) :
    (j / 2 ^ t % 2 = 1 → spread_P (t + 1) j + 10 * 2 ^ t = spread_P t j) ∧
    (j / 2 ^ t % 2 ≠ 1 → spread_P (t + 1) j = spread_P t j) := by
  unfold spread_P
  have hd : j / 2 ^ (t + 1) = j / 2 ^ t / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hd, Nat.pow_succ]
  generalize j / 2 ^ t = d
  have hk : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
  generalize d / 2 = k at hk
  constructor
  · intro h1
    rw [h1] at hk
    subst hk
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.one_mul]
    omega
  · intro h1
    have h0 : d % 2 = 0 := by omega
    rw [h0] at hk
    subst hk
    simp only [Nat.add_zero, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem spread_and_seven {a : Nat} (ha : a < 8) : a &&& 7 = a := by
  rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt ha

theorem spread_step (t : Nat) (f : Nat → Nat) (hf : ∀ j, f j < 8) (N : Nat) :
    (spread_V (spread_P (t + 1)) f N ^^^ (spread_V (spread_P (t + 1)) f N &&&
        spread_V (spread_P (t + 1)) (spread_g t) N)) |||
      ((spread_V (spread_P (t + 1)) f N &&& spread_V (spread_P (t + 1)) (spread_g t) N) <<<
        (10 * 2 ^ t)) = spread_V (spread_P t) f N := by
  have hg : ∀ j, spread_g t j < 8 := by intro j; unfold spread_g; split <;> omega
  let fa : Nat → Nat := fun j => if j / 2 ^ t % 2 = 1 then f j else 0
  let fb : Nat → Nat := fun j => if j / 2 ^ t % 2 = 1 then 0 else f j
  have hfa : ∀ j, fa j < 8 := by intro j; simp only [fa]; split <;> simp [hf]
  have hfb : ∀ j, fb j < 8 := by intro j; simp only [fb]; split <;> simp [hf]
  have hsep := spread_P_sep (t + 1)
  have e1 : spread_V (spread_P (t + 1)) f N &&& spread_V (spread_P (t + 1)) (spread_g t) N =
      spread_V (spread_P (t + 1)) fa N := by
    rw [spread_V_and _ _ _ hsep hf hg]
    apply spread_V_congr_coef
    intro j _
    simp only [spread_g, fa]
    split
    · exact spread_and_seven (hf j)
    · exact Nat.and_zero _
  rw [e1, spread_V_xor _ _ _ hsep hf hfa, spread_V_shiftLeft]
  have e2 : spread_V (spread_P (t + 1)) (fun j => f j ^^^ fa j) N =
      spread_V (spread_P t) fb N := by
    rw [spread_V_congr_coef _ _ fb]
    · apply spread_V_congr_pos
      intro j _
      by_cases h : j / 2 ^ t % 2 = 1
      · left; simp [fb, h]
      · right; exact (spread_P_step t j).2 h
    · intro j _
      simp only [fa, fb]
      split
      · exact Nat.xor_self _
      · exact Nat.xor_zero _
  have e3 : spread_V (fun j => spread_P (t + 1) j + 10 * 2 ^ t) fa N =
      spread_V (spread_P t) fa N := by
    apply spread_V_congr_pos
    intro j _
    by_cases h : j / 2 ^ t % 2 = 1
    · right; exact (spread_P_step t j).1 h
    · left; simp [fa, h]
  rw [e2, e3, spread_V_or _ _ _ (spread_P_sep t) hfb hfa]
  apply spread_V_congr_coef
  intro j _
  simp only [fa, fb]
  split
  · exact Nat.zero_or _
  · exact Nat.or_zero _

theorem spread_rec_succ {α : Type} (z : α) (F : Nat → α → α) (n : Nat) :
    (Nat.rec (motive := fun _ => α) z F (n + 1) : α) = F n (Nat.rec (motive := fun _ => α) z F n) :=
  rfl

theorem spread_rec_inv {α : Type} (z : α) (F : Nat → α → α) (P : Nat → α → Prop) (h0 : P 0 z)
    (hs : ∀ n a, P n a → P (n + 1) (F n a)) : ∀ n, P n (Nat.rec (motive := fun _ => α) z F n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n _ ih

theorem spread_g_lt (t : Nat) : ∀ j, spread_g t j < 8 := by
  intro j; unfold spread_g; split <;> omega

theorem spread_maskB_rec (t n : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => nIf(Nat.beq (Nat.land (Nat.shiftRight j t) (nat_lit 1)) (nat_lit 1),
        Nat.lor acc (Nat.shiftLeft (nat_lit 7) (Nat.add (Nat.mul (nat_lit 3) j)
          (Nat.mul (nat_lit 10) (Nat.shiftLeft (Nat.shiftRight j (Nat.succ t)) (Nat.succ t))))), acc))
      n : Nat) = spread_V (spread_P (t + 1)) (spread_g t) n := by
  refine spread_rec_inv _ _ (fun n a => a = spread_V (spread_P (t + 1)) (spread_g t) n) rfl ?_ n
  intro n a ha
  subst ha
  beta_reduce
  rw [spread_V_succ]
  have hb : Nat.land (Nat.shiftRight n t) 1 = n / 2 ^ t % 2 := by
    change n >>> t &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hp : Nat.add (Nat.mul 3 n) (Nat.mul 10 (Nat.shiftLeft (Nat.shiftRight n (Nat.succ t))
      (Nat.succ t))) = spread_P (t + 1) n := by
    change 3 * n + 10 * ((n >>> (t + 1)) <<< (t + 1)) = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rfl
  have hlt := spread_V_lt (spread_P (t + 1)) (spread_g t) (spread_P_sep (t + 1)) (spread_g_lt t) n
  rw [hb, hp]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ t) with h | h
  · have hg : spread_g t n = 0 := by simp [spread_g, h]
    rw [hg, h]
    show spread_V (spread_P (t + 1)) (spread_g t) n = _
    simp
  · have hg : spread_g t n = 7 := by simp [spread_g, h]
    rw [hg, h]
    show spread_V (spread_P (t + 1)) (spread_g t) n ||| 7 <<< spread_P (t + 1) n = _
    rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm 7, ← Nat.two_pow_add_eq_or_of_lt hlt]
    ring

theorem spread_maskB (i : Nat) :
    maskB i = spread_V (spread_P (7 - i + 1)) (spread_g (7 - i)) 133 :=
  spread_maskB_rec (7 - i) 133

theorem spread_bAnd {b c : Bool} (h : (Bool.rec (motive := fun _ => Bool) false b c : Bool) = true) :
    b = true ∧ c = true := by
  cases c
  · exact absurd h Bool.false_ne_true
  · exact ⟨h, rfl⟩

theorem spread_masks_rec (MS n : Nat)
    (h : (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (fldW MS (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (maskB i), ih))
      n : Bool) = true) : ∀ i < n, fldW MS (1729 * i) 1729 = maskB i := by
  revert h
  refine spread_rec_inv _ _
    (fun n a => a = true → ∀ i < n, fldW MS (1729 * i) 1729 = maskB i) (fun _ i hi => by omega) ?_ n
  intro n a ih h
  obtain ⟨h1, h2⟩ := spread_bAnd h
  intro i hi
  rcases Nat.lt_or_ge i n with hi' | hi'
  · exact ih h1 i hi'
  · have : i = n := by omega
    subst this
    exact Nat.eq_of_beq_eq_true h2

theorem spread_masks {MS : Nat} (hm : masksOK MS = true) :
    ∀ i < 8, fldW MS (1729 * i) 1729 = maskB i :=
  spread_masks_rec MS 8 (spread_bAnd hm).1

theorem spread_mod (x N : Nat) :
    x % 2 ^ (3 * N) = spread_V (fun j => 3 * j) (fun j => x / 2 ^ (3 * j) % 8) N := by
  induction N with
  | zero => simp [spread_V_zero, Nat.mod_one]
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 3 by omega, Nat.pow_add, Nat.mod_mul, ih, spread_V_succ,
      Nat.mul_comm (2 ^ (3 * N))]

theorem spread_init {x : Nat} (hx : x < 2 ^ 399) :
    x = spread_V (spread_P 8) (fun j => x / 2 ^ (3 * j) % 8) 133 := by
  have h1 := spread_mod x 133
  rw [Nat.mod_eq_of_lt (show x < 2 ^ (3 * 133) from hx)] at h1
  refine h1.trans ?_
  apply spread_V_congr_pos
  intro j hj
  right
  unfold spread_P
  have : j / 2 ^ 8 = 0 := Nat.div_eq_of_lt (by norm_num; omega)
  rw [this]; simp

theorem spread_P_zero : spread_P 0 = fun j => 13 * j := by
  funext j; unfold spread_P; simp; omega

theorem spread_extract (u : Nat → Nat) (hu : ∀ j, u j < 8) :
    ∀ N, ∀ l < N, spread_V (fun j => 13 * j) u N / 2 ^ (13 * l) % 2 ^ 13 = u l := by
  have hsep : ∀ j, 13 * j + 3 ≤ 13 * (j + 1) := by intro j; omega
  intro N
  induction N with
  | zero => intro l hl; omega
  | succ N ih =>
    intro l hl
    rw [spread_V_succ]
    rcases Nat.lt_or_ge l N with hl' | hl'
    · have e : u N * 2 ^ (13 * N) = (u N * 2 ^ (13 * (N - l - 1)) * 2 ^ 13) * 2 ^ (13 * l) := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
        congr 2
        omega
      rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right, ih l hl']
    · have : l = N := by omega
      subst this
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (spread_V_lt (fun j => 13 * j) u hsep hu l), Nat.zero_add,
        Nat.mod_eq_of_lt (lt_of_lt_of_le (hu l) (by norm_num))]

theorem spread_iter {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    ∀ k ≤ 8, (Nat.rec (motive := fun _ => Nat) x
      (fun i acc => CFSG.KC.Loop.strictN acc (fun a => sp1 a (fldW MS (Nat.mul (nat_lit 1729) i)
        (nat_lit 1729)) (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i)))))
      k : Nat) = spread_V (spread_P (8 - k)) (fun j => x / 2 ^ (3 * j) % 8) 133 := by
  have hf : ∀ j, x / 2 ^ (3 * j) % 8 < 8 := fun j => Nat.mod_lt _ (by omega)
  refine spread_rec_inv _ _
    (fun k a => k ≤ 8 → a = spread_V (spread_P (8 - k)) (fun j => x / 2 ^ (3 * j) % 8) 133)
    (fun _ => spread_init hx) ?_
  intro k a ih hk
  beta_reduce
  rw [ih (by omega), loopStrictN_eq]
  unfold sp1
  rw [loopStrictN_eq]
  show (spread_V (spread_P (8 - k)) _ 133 ^^^
      (spread_V (spread_P (8 - k)) _ 133 &&& fldW MS (1729 * k) 1729)) |||
    ((spread_V (spread_P (8 - k)) _ 133 &&& fldW MS (1729 * k) 1729) <<< (10 * (1 <<< (7 - k))))
    = _
  rw [spread_masks hm k (by omega), spread_maskB k, show 8 - k = 7 - k + 1 by omega,
    show 8 - (k + 1) = 7 - k by omega, Nat.one_shiftLeft]
  exact spread_step (7 - k) _ hf 133

theorem spread_eq {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    spread MS x = spread_V (fun j => 13 * j) (fun j => x / 2 ^ (3 * j) % 8) 133 := by
  rw [← spread_P_zero]
  exact spread_iter hm hx 8 le_rfl

theorem spread_lane {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    ∀ l < 133, spread MS x / 2 ^ (13 * l) % 2 ^ 13 = x / 2 ^ (3 * l) % 8 := by
  rw [spread_eq hm hx]
  exact spread_extract _ (fun j => Nat.mod_lt _ (by omega)) 133

theorem spread_lane' {MS x : Nat} (hm : masksOK MS = true) (hx : x < 2 ^ 399) :
    ∀ l < 133, spread MS x / 2 ^ (13 * l) % 2 ^ 13 = x / 2 ^ (3 * l) % 8 :=
  spread_lane hm hx

end CFSG.KS.SporSch.HNXP

end
