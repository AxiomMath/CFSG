
module

public import Certificates.Data.Kernel.SporSch.ThOrb
public import CFSG.Certificates.Kernel.SporSch.ThRowsSoundBase
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier

theorem rmP_eq : rmP = 2 ^ 248 - 1 := by
  have e : Nat.shiftLeft 1 248 = 2 ^ 248 := (Nat.shiftLeft_eq 1 248).trans (Nat.one_mul _)
  exact congrArg (fun x => x - 1) e

theorem unpk_lt (M i : Nat) : unpk M i < 2 ^ 248 := by
  unfold unpk
  rw [rmP_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos 248) Nat.one_pos)

theorem strictN_val' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] def opXs (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => opXs g n ^^^ g n

@[expose] def opBx (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => Bool.xor (opBx p n) (p n)

theorem opXs_succ (g : Nat → Nat) (n : Nat) : opXs g (n + 1) = opXs g n ^^^ g n := rfl

theorem opXs_add (g : Nat → Nat) (a : Nat) :
    ∀ c, opXs g (a + c) = opXs g a ^^^ opXs (fun l => g (a + l)) c
  | 0 => (Nat.xor_zero _).symm
  | c + 1 => by
    rw [← Nat.add_assoc, opXs_succ, opXs_succ, opXs_add g a c, Nat.xor_assoc]

theorem testBit_opXs (g : Nat → Nat) (s : Nat) :
    ∀ n, (opXs g n).testBit s = opBx (fun l => (g l).testBit s) n
  | 0 => Nat.zero_testBit s
  | n + 1 => (Nat.testBit_xor ..).trans
      (congrArg (fun b => Bool.xor b ((g n).testBit s)) (testBit_opXs g s n))

theorem opBx_congr {p p' : Nat → Bool} : ∀ {n}, (∀ k < n, p k = p' k) → opBx p n = opBx p' n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := opBx_congr (n := n) fun k hk => h k (by omega)
    have hn := h n (by omega)
    change Bool.xor (opBx p n) (p n) = Bool.xor (opBx p' n) (p' n)
    rw [ih, hn]

theorem opBx_false : ∀ n, opBx (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by
    change Bool.xor (opBx (fun _ => false) n) false = false
    rw [opBx_false n]
    rfl

theorem opFoldBlk_xor {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i a, f i a = a ^^^ g i)
    (b : Nat) : ∀ len s, foldBlk b f len s = s ^^^ opXs (fun l => g (b + l)) len
  | 0, s => (Nat.xor_zero s).symm
  | len + 1, s => by
    have e : foldBlk b f (len + 1) s = foldBlk b f len (f (Nat.add b len) s) :=
      strictN_val' (f (Nat.add b len) s) (foldBlk b f len)
    rw [e, opFoldBlk_xor hf b len, hf, opXs_succ, Nat.xor_assoc]
    exact congrArg (fun t => s ^^^ t) (Nat.xor_comm _ _)

@[expose] noncomputable def opRec (f : Nat → Nat → Nat) (q : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q

theorem opShl6 (q : Nat) : Nat.shiftLeft q 6 = 64 * q := by
  change q <<< 6 = 64 * q
  rw [Nat.shiftLeft_eq]
  ring

theorem opRec_xor {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i a, f i a = a ^^^ g i) :
    ∀ q t, opRec f q t = t ^^^ opXs g (64 * q)
  | 0, t => (Nat.xor_zero t).symm
  | q + 1, t => by
    have e : opRec f (q + 1) t = opRec f q (foldBlk (Nat.shiftLeft q 6) f 64 t) :=
      strictN_val' (foldBlk (Nat.shiftLeft q 6) f 64 t) (opRec f q)
    have hm : 64 * (q + 1) = 64 * q + 64 := by ring
    rw [e, opRec_xor hf q, opFoldBlk_xor hf, opShl6, hm, opXs_add, Nat.xor_assoc]
    exact congrArg (fun x => t ^^^ x) (Nat.xor_comm _ _)

theorem opFoldN_xor {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i a, f i a = a ^^^ g i)
    (n s : Nat) : foldN n f s = s ^^^ opXs g n := by
  have h0 : foldN n f s =
      opRec f (Nat.shiftRight n 6) (foldBlk (Nat.shiftLeft (Nat.shiftRight n 6) 6) f (Nat.land n 63) s) :=
    rfl
  have h1 : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = n / 64
    simp [Nat.shiftRight_eq_div_pow]
  have h2 : Nat.land n 63 = n % 64 := by
    have := Nat.and_two_pow_sub_one_eq_mod n 6
    simpa using this
  rw [h0, opRec_xor hf, opFoldBlk_xor hf, h1, h2, opShl6]
  conv_rhs => rw [← Nat.div_add_mod n 64]
  rw [opXs_add, Nat.xor_assoc]
  exact congrArg (fun x => s ^^^ x) (Nat.xor_comm _ _)

@[expose] def opBlk (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => opBlk f n + f n * 2 ^ (256 * n)

theorem opBlk_zero (f : Nat → Nat) : opBlk f 0 = 0 := rfl

theorem opBlk_succ (f : Nat → Nat) (n : Nat) : opBlk f (n + 1) = opBlk f n + f n * 2 ^ (256 * n) :=
  rfl

theorem opBlk_lt {f : Nat → Nat} (hf : ∀ r, f r < 2 ^ 256) : ∀ n, opBlk f n < 2 ^ (256 * n)
  | 0 => by
    rw [opBlk_zero]
    exact Nat.two_pow_pos _
  | n + 1 => by
    have ih := opBlk_lt hf n
    have h1 : f n + 1 ≤ 2 ^ 256 := hf n
    have e : 256 * (n + 1) = 256 * n + 256 := by ring
    rw [opBlk_succ, e, Nat.pow_add]
    calc opBlk f n + f n * 2 ^ (256 * n) < 2 ^ (256 * n) + f n * 2 ^ (256 * n) :=
          Nat.add_lt_add_right ih _
      _ = (f n + 1) * 2 ^ (256 * n) := by ring
      _ ≤ 2 ^ 256 * 2 ^ (256 * n) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (256 * n) * 2 ^ 256 := Nat.mul_comm _ _

theorem testBit_opBlk {f : Nat → Nat} (hf : ∀ r, f r < 2 ^ 256) {s : Nat} (hs : s < 256) :
    ∀ n q, (opBlk f n).testBit (256 * q + s) = (decide (q < n) && (f q).testBit s)
  | 0, q => by
    rw [opBlk_zero, Nat.zero_testBit]
    simp
  | n + 1, q => by
    have hlt := opBlk_lt hf n
    rw [opBlk_succ, Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hlt,
      Nat.testBit_or, Nat.testBit_shiftLeft, testBit_opBlk hf hs n q]
    rcases Nat.lt_trichotomy q n with h | h | h
    · have h1 : ¬ (256 * n ≤ 256 * q + s) := by omega
      have h2 : q < n + 1 := by omega
      simp [h, h1, h2]
    · have h1 : 256 * q + s - 256 * n = s := by omega
      have h2 : 256 * n ≤ 256 * q + s := by omega
      have h3 : q < n + 1 := by omega
      have h4 : ¬ q < n := by omega
      rw [h1]
      simp [h2, h3, h4, h]
    · have h1 : 256 * n ≤ 256 * q + s := by omega
      have h3 : ¬ q < n + 1 := by omega
      have h4 : ¬ q < n := by omega
      have h5 : (f n).testBit (256 * q + s - 256 * n) = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (hf n) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, h3, h4, h5]

theorem opBlk_mul (f : Nat → Nat) (c : Nat) : ∀ n, opBlk f n * c = opBlk (fun r => f r * c) n
  | 0 => by rw [opBlk_zero, opBlk_zero, Nat.zero_mul]
  | n + 1 => by rw [opBlk_succ, opBlk_succ, Nat.add_mul, opBlk_mul f c n, Nat.mul_right_comm]

theorem mul_opBlk (c : Nat) (f : Nat → Nat) : ∀ n, c * opBlk f n = opBlk (fun r => c * f r) n
  | 0 => by rw [opBlk_zero, opBlk_zero, Nat.mul_zero]
  | n + 1 => by rw [opBlk_succ, opBlk_succ, Nat.mul_add, mul_opBlk c f n, ← Nat.mul_assoc]

theorem ccP_chk : Nat.beq ccP (opBlk (fun _ => 1) 248) = true := by quickRfl

theorem ccP_eq : ccP = opBlk (fun _ => 1) 248 := Nat.eq_of_beq_eq_true ccP_chk

theorem one_testBit' : ∀ s, (1 : Nat).testBit s = decide (s = 0)
  | 0 => rfl
  | s + 1 => by
    rw [Nat.testBit_succ]
    simp

theorem and_ccP (x : Nat) :
    x &&& ccP = opBlk (fun r => if x.testBit (256 * r) = true then 1 else 0) 248 := by
  apply Nat.eq_of_testBit_eq
  intro j
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 256 ∧ j = 256 * q + s :=
    ⟨j / 256, j % 256, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 256).symm⟩
  rw [Nat.testBit_and, ccP_eq, testBit_opBlk (f := fun _ => 1) (fun _ => by norm_num) hs,
    testBit_opBlk (f := fun r => if x.testBit (256 * r) = true then 1 else 0)
      (fun r => by beta_reduce; split <;> norm_num) hs]
  by_cases h0 : s = 0
  · subst h0
    cases hx : x.testBit (256 * q) <;> simp [hx, one_testBit']
  · cases hx : x.testBit (256 * q) <;> simp [hx, one_testBit', h0]

@[expose] noncomputable def opStep (A B k : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) ccP) rmP)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul k (nat_lit 256))) rmP) ccP)

theorem mulPk_xs (A B : Nat) : mulPk A B = opXs (opStep A B) 248 := by
  have key : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.xor acc (opStep A B k)) n = opXs (opStep A B) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun t => Nat.xor t (opStep A B n)) ih
  exact key 248

theorem unpk_testBit (M i s : Nat) :
    (unpk M i).testBit s = (decide (s < 248) && M.testBit (256 * i + s)) := by
  have e : unpk M i = (M >>> (i * 256)) &&& rmP := rfl
  rw [e, rmP_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm, Nat.mul_comm i 256]

theorem stepBit (A B k : Nat) {i s : Nat} (hi : i < 248) (hs : s < 248) :
    (opStep A B k).testBit (256 * i + s) = (A.testBit (k + 256 * i) && (unpk B k).testBit s) := by
  have e : opStep A B k = ((A >>> k) &&& ccP) * rmP &&& (unpk B k * ccP) := rfl
  have hr : rmP < 2 ^ 256 := by
    rw [rmP_eq]
    norm_num
  have hy : unpk B k < 2 ^ 256 := lt_trans (unpk_lt B k) (by norm_num)
  have hs' : s < 256 := by omega
  rw [e, Nat.testBit_and, and_ccP, opBlk_mul, ccP_eq, mul_opBlk,
    testBit_opBlk (f := fun r => (if (A >>> k).testBit (256 * r) = true then 1 else 0) * rmP)
      (fun r => by
        beta_reduce
        split
        · rw [Nat.one_mul]
          exact hr
        · rw [Nat.zero_mul]
          exact Nat.two_pow_pos _) hs',
    testBit_opBlk (f := fun _ => unpk B k * 1) (fun _ => by rw [Nat.mul_one]; exact hy) hs']
  have hR : rmP.testBit s = true := by
    rw [rmP_eq, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hs
  simp only [decide_eq_true hi, Bool.true_and, Nat.mul_one, Nat.testBit_shiftRight]
  cases hA : A.testBit (k + 256 * i)
  · simp
  · simp only [ite_true, Nat.one_mul, hR, Bool.true_and]

theorem mulPk_row (A B i : Nat) (hi : i < 248) :
    unpk (mulPk A B) i = vmT (unpk B) (unpk A i) := by
  have hf : ∀ j acc, (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (unpk B j))
      (Nat.blt 0 (Nat.land (unpk A i) (Nat.shiftLeft 1 j)))) j acc =
      acc ^^^ (fun j => if (unpk A i).testBit j = true then unpk B j else 0) j := by
    intro j acc
    have e1 : Nat.shiftLeft 1 j = 2 ^ j := (Nat.shiftLeft_eq 1 j).trans (Nat.one_mul _)
    have e : Nat.land (unpk A i) (Nat.shiftLeft 1 j) = ((unpk A i).testBit j).toNat * 2 ^ j := by
      rw [e1]
      exact Nat.and_two_pow _ _
    beta_reduce
    rw [e]
    cases hb : (unpk A i).testBit j
    · rw [Bool.toNat_false, Nat.zero_mul]
      have z : Nat.blt 0 0 = false := rfl
      exact (congrArg (fun c => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (unpk B j)) c)
        z).trans (Nat.xor_zero acc).symm
    · rw [Bool.toNat_true, Nat.one_mul]
      have z : Nat.blt 0 (2 ^ j) = true := Nat.blt_eq.mpr (Nat.two_pow_pos j)
      exact congrArg (fun c => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (unpk B j)) c) z
  have hv : vmT (unpk B) (unpk A i) =
      0 ^^^ opXs (fun j => if (unpk A i).testBit j = true then unpk B j else 0) 248 :=
    opFoldN_xor hf 248 0
  apply Nat.eq_of_testBit_eq
  intro s
  rw [hv, Nat.zero_xor, unpk_testBit (mulPk A B) i s, mulPk_xs, testBit_opXs, testBit_opXs]
  by_cases hs : s < 248
  · rw [decide_eq_true hs, Bool.true_and]
    apply opBx_congr
    intro k hk
    beta_reduce
    rw [stepBit A B k hi hs, unpk_testBit A i k, decide_eq_true hk, Bool.true_and,
      Nat.add_comm k (256 * i)]
    cases A.testBit (256 * i + k) <;> simp
  · have hz : ∀ k < 248,
        (fun l => (if (unpk A i).testBit l = true then unpk B l else 0).testBit s) k =
          (fun _ => false) k := by
      intro k _
      beta_reduce
      split <;> simp [unpk_testBit, hs]
    rw [decide_eq_false hs, Bool.false_and, opBx_congr hz, opBx_false]

theorem mulPk_sound (A B : Nat) :
    mulRows (rowsV (unpk A)) (rowsV (unpk B)) = rowsV (unpk (mulPk A B)) :=
  mulRows_sound (fun i _ => unpk_lt A i) (fun i _ => unpk_lt B i)
    (fun i hi => (mulPk_row A B i hi).symm)

theorem v4_eq_of_beq {a b : V4} (h : a.beq b = true) : a = b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [V4.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  rw [h0, h1, h2, h3]

theorem eqRows_refl (X : Array V4) : eqRows X X = true := by
  simp [eqRows, V4.beq]

theorem eqRows_sound {R R' : Nat → Nat} (hR : ∀ i < 248, R i < 2 ^ 248)
    (hR' : ∀ i < 248, R' i < 2 ^ 248) (h : eqRows (rowsV R) (rowsV R') = true) :
    ∀ i < 248, R i = R' i := by
  intro i hi
  simp only [eqRows, rowsV, Array.size_ofFn, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    List.mem_range] at h
  have hb := h i hi
  simp only [Array.getElem?_ofFn, hi, dite_true, Option.getD_some] at hb
  have e := congrArg V4.toNat (v4_eq_of_beq hb)
  rw [v4OfNat_toNat, v4OfNat_toNat, Nat.mod_eq_of_lt (Nat.lt_trans (hR i hi) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_trans (hR' i hi) (by norm_num))] at e
  exact e

theorem repk_congr {R R' : Nat → Nat} (h : ∀ i < 248, R i = R' i) : repk R = repk R' := by
  have key : ∀ n ≤ 248,
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.lor acc (Nat.shiftLeft (R i) (Nat.mul i (nat_lit 256)))) n =
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.lor acc (Nat.shiftLeft (R' i) (Nat.mul i (nat_lit 256)))) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have e := ih (by omega)
      simp only at e ⊢
      rw [e, h n (by omega)]
  exact key 248 le_rfl

theorem strictB_val' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_val (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIf_val (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem letPk_spec (A B BB : Nat) (z : Int) :
    letPk A B BB z = if z = 1 ∨ z = -1 then A else if z = 2 then B else BB := by
  have r2 : ∀ c, Nat.beq c (nat_lit 2) = Nat.beq c 2 := fun _ => rfl
  have r3 : ∀ c, Nat.beq c (nat_lit 3) = Nat.beq c 3 := fun _ => rfl
  have r4 : ∀ c, Nat.beq c (nat_lit 4) = Nat.beq c 4 := fun _ => rfl
  unfold letPk
  simp only [strictN_val', r2, r3, r4, nIf_val, Nat.beq_eq]
  rcases z with k | k
  · have e : CFSG.KS.Mathieu.icode (Int.ofNat k) = k + k := rfl
    rw [e]
    simp only [Int.ofNat_eq_natCast]
    rcases (by omega : k = 1 ∨ k = 2 ∨ (k ≠ 1 ∧ k ≠ 2)) with h | h | ⟨h1, h2⟩
    · subst h
      simp
    · subst h
      simp
    · have a2 : ¬ k + k = 2 := by omega
      have a3 : ¬ k + k = 3 := by omega
      have a4 : ¬ k + k = 4 := by omega
      have b1 : ¬ ((k : Int) = 1 ∨ (k : Int) = -1) := by omega
      have b2 : ¬ (k : Int) = 2 := by omega
      simp only [a2, a3, a4, b1, b2, ite_false]
  · have e : CFSG.KS.Mathieu.icode (Int.negSucc k) = (k + 1) + (k + 1) + 1 := rfl
    rw [e]
    simp only [Int.negSucc_eq]
    rcases (by omega : k = 0 ∨ k ≠ 0) with h | h
    · subst h
      simp
    · have a2 : ¬ k + 1 + (k + 1) + 1 = 2 := by omega
      have a3 : ¬ k + 1 + (k + 1) + 1 = 3 := by omega
      have a4 : ¬ k + 1 + (k + 1) + 1 = 4 := by omega
      have b1 : ¬ (-((k : Int) + 1) = 1 ∨ -((k : Int) + 1) = -1) := by omega
      have b2 : ¬ -((k : Int) + 1) = 2 := by omega
      simp only [a2, a3, a4, b1, b2, ite_false]

theorem entK_spec {S SG TU PAR LAB EDG : Nat → Nat} {T X Y YY i : Nat}
    (h : entK S SG TU PAR LAB EDG T X Y YY i = true) :
    SG i < 819 ∧ TU (SG i) = i ∧ (i = 0 → S (SG i) = T) ∧
      (i ≠ 0 → PAR i < i ∧ (LAB i = 1 ∨ LAB i = 2) ∧ EDG (2 * PAR i + (LAB i - 1)) = i) ∧
      EDG (2 * i) < 819 ∧ EDG (2 * i + 1) < 819 ∧
      mulPk (mulPk X (S (SG i))) X = S (SG (EDG (2 * i))) ∧
      mulPk (mulPk Y (S (SG i))) YY = S (SG (EDG (2 * i + 1))) := by
  unfold entK at h
  rw [strictB_val'] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  unfold edgK at h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h
  have e2 : 2 * i = Nat.add i i := by rw [Nat.add_eq]; omega
  have e3 : 2 * i + 1 = Nat.succ (Nat.add i i) := by rw [Nat.add_eq]; omega
  rw [bIf_val] at h3
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hi => ?_, fun hi => ?_, ?_, ?_, ?_, ?_⟩
  · have hb : Nat.beq i 0 = true := by rw [hi]; rfl
    rw [ite_eq_left hb] at h3
    exact Nat.eq_of_beq_eq_true h3
  · have hb : ¬ Nat.beq i 0 = true := fun h' => hi (Nat.eq_of_beq_eq_true h')
    rw [ite_eq_right hb] at h3
    unfold parPk at h3
    obtain ⟨p1, h3⟩ := (bAnd_iff _ _).1 h3
    obtain ⟨p2, p3⟩ := (bAnd_iff _ _).1 h3
    rw [bIf_val] at p2
    refine ⟨Nat.blt_eq.mp p1, ?_, ?_⟩
    · by_cases hl : Nat.beq (LAB i) 1 = true
      · exact Or.inl (Nat.eq_of_beq_eq_true hl)
      · rw [ite_eq_right hl] at p2
        exact Or.inr (Nat.eq_of_beq_eq_true p2)
    · have e : 2 * PAR i + (LAB i - 1) = Nat.add (Nat.add (PAR i) (PAR i)) (Nat.sub (LAB i) 1) := by
        rw [Nat.add_eq, Nat.add_eq, Nat.sub_eq]
        omega
      rw [e]
      exact Nat.eq_of_beq_eq_true p3
  · rw [e2]
    exact Nat.blt_eq.mp h4
  · rw [e3]
    exact Nat.blt_eq.mp h5
  · rw [e2]
    exact Nat.eq_of_beq_eq_true h6
  · rw [e3]
    exact Nat.eq_of_beq_eq_true h7

theorem srtK_spec {S : Nat → Nat} {k : Nat} (h : srtK S k = true) :
    repk (unpk (S k)) = S k ∧ (k < 818 → S k < S (k + 1)) := by
  unfold srtK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [bIf_val] at h2
  refine ⟨Nat.eq_of_beq_eq_true h1, fun hk => ?_⟩
  rw [ite_eq_left (Nat.blt_eq.mpr hk)] at h2
  exact Nat.blt_eq.mp h2

end CFSG.KS.SporSch

end
