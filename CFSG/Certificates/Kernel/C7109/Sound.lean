module

public import Certificates.Data.Kernel.C7109.Check
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.C7109

open Matrix

@[expose] def matOf (m : ℕ) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if m.testBit (5 * (i : ℕ) + j) then 1 else 0

@[expose] def vdec (v : ℕ) : Fin 5 → ZMod 2 := fun i => if v.testBit i then 1 else 0

@[expose] noncomputable def symC (p : ℕ) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if p.testBit (fd 4 symIdx (5 * (i : ℕ) + j)) then 1 else 0

@[expose] noncomputable def lane (MT i : ℕ) : ℕ := fd 25 MT i

@[expose] def recAt (RL : List ℕ) (i : ℕ) : ℕ := RL.getD i 0

@[expose] def IsUni (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  (∀ i j : Fin 5, j < i → M i j = 0) ∧ ∀ i, M i i = 1

@[expose] noncomputable def andMask (sel : ℕ → ℕ) (RL : List ℕ) (X : Finset ℕ) : ℕ :=
  (List.range 191).foldr
    (fun a acc => if a ∈ X then Nat.land (sel (recAt RL a)) acc else acc) 4294967295

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem eqB_eq (a b : Bool) : eqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl

theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

theorem shr_eq (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

theorem fd_eq (w x i : ℕ) : fd w x i = (x >>> (w * i)) % 2 ^ w := by
  unfold fd
  rw [land_eq, shr_eq, shl_eq, Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem bitB_eq (x i : ℕ) : bitB x i = x.testBit i := by
  unfold bitB
  rw [land_eq, shl_eq, Nat.shiftLeft_eq, one_mul, Bool.eq_iff_iff, Nat.blt_eq]
  have key : ∀ j, (x &&& 2 ^ i).testBit j = (x.testBit i && decide (i = j)) := by
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h
      rfl
    · simp [h]
  constructor
  · intro hpos
    by_contra hb
    have h0 : x &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [key, Nat.zero_testBit]
      simp [hb]
    omega
  · intro hb
    apply Nat.pos_of_ne_zero
    intro h0
    have h1 := key i
    rw [h0, Nat.zero_testBit, hb] at h1
    simp at h1

theorem testBit_mask (n p : ℕ) : (Nat.sub (Nat.shiftLeft 1 n) 1).testBit p = decide (p < n) := by
  rw [Nat.sub_eq, shl_eq, Nat.shiftLeft_eq, one_mul]
  exact Nat.testBit_two_pow_sub_one _ _

theorem testBit_full {p : ℕ} : full.testBit p = decide (p < 32768) := testBit_mask W p

theorem nodeOK_sound {S k f fT : ℕ} {B : List ℕ} (h : nodeOK S k f fT B = true) :
    ((k = 5 ∨ k = 6) → (pop32 f = 4 ∧ pop32 fT = 8) ∨ (pop32 f = 8 ∧ pop32 fT = 4)) ∧
      (k = 4 → pop32 f = pop32 fT → formOK S B = true) := by
  unfold nodeOK at h
  simp only [letB_eq, orB_eq, andB_eq] at h
  refine ⟨fun hk => ?_, fun hk hab => ?_⟩
  · have hc : (Nat.beq k 5 || Nat.beq k 6) = true := by
      rcases hk with rfl | rfl <;> rfl
    rw [hc] at h
    dsimp only at h
    simpa [Nat.beq_eq] using h
  · subst hk
    have hc : (Nat.beq 4 5 || Nat.beq 4 6) = false := rfl
    have h4 : Nat.beq 4 4 = true := rfl
    rw [hc, h4, hab, Nat.beq_refl] at h
    exact h

theorem ffS_cons (r : ℕ) (B : List ℕ) : ffS (r :: B) = Nat.land (ffS B) (ffG (rM r)) := by
  change letN (ffS B) (fun a => Nat.land a (ffG (rM r))) = _
  rw [letN_eq]

theorem testBit_ffS (B : List ℕ) (p : ℕ) :
    (ffS B).testBit p = true ↔ p < 32768 ∧ ∀ r ∈ B, (ffG (rM r)).testBit p = true := by
  induction B with
  | nil =>
    change full.testBit p = true ↔ _
    simp [testBit_full]
  | cons r B ih =>
    rw [ffS_cons, land_eq, Nat.testBit_and, Bool.and_eq_true, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem formOK_sound {S : ℕ} {B : List ℕ} (h : formOK S B = true) (p : ℕ) (hp : p < 2 ^ 15)
    (hB : ∀ r ∈ B, (ffG (rM r)).testBit p) : S.testBit p := by
  unfold formOK at h
  have h0 := congrArg (fun n => n.testBit p) (Nat.eq_of_beq_eq_true h)
  have hp' : p < 32768 := lt_of_lt_of_le hp (by norm_num)
  have hf : (ffS B).testBit p = true := (testBit_ffS B p).2 ⟨hp', hB⟩
  simp only [land_eq, xor_eq, Nat.testBit_and, Nat.testBit_xor, testBit_full, hf,
    Nat.zero_testBit, hp'] at h0
  simpa using h0

theorem bits_add (a b x : ℕ) :
    (∑ v ∈ Finset.range (a + b), if x.testBit v then 1 else 0) =
      (∑ v ∈ Finset.range a, if x.testBit v then 1 else 0) +
        ∑ v ∈ Finset.range b, if (x >>> a).testBit v then 1 else 0 := by
  rw [Finset.sum_range_add]
  simp only [Nat.testBit_shiftRight]

theorem bits8_mod (y : ℕ) : (∑ v ∈ Finset.range 8, if (y % 2 ^ 8).testBit v then 1 else 0) =
    ∑ v ∈ Finset.range 8, if y.testBit v then 1 else 0 := by
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Nat.testBit_mod_two_pow]
  simp [Finset.mem_range.1 hv]

theorem popT_spec : ∀ b < 256,
    fd 4 popT b = ∑ v ∈ Finset.range 8, if b.testBit v then 1 else 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  decide +kernel

theorem pop_byte (x i : ℕ) : fd 4 popT (fd 8 x i) =
    ∑ v ∈ Finset.range 8, if (x >>> (8 * i)).testBit v then 1 else 0 := by
  have hl : fd 8 x i < 256 := by
    rw [fd_eq]
    exact Nat.mod_lt _ (by norm_num)
  rw [popT_spec _ hl, fd_eq, bits8_mod]

theorem pop32_spec {x : ℕ} (hx : x < 2 ^ 32) :
    pop32 x = ((Finset.range 32).filter fun v => x.testBit v).card := by
  rw [Finset.card_filter]
  have h32 : (32 : ℕ) = 8 + (8 + (8 + 8)) := rfl
  rw [h32, bits_add, bits_add, bits_add]
  unfold pop32
  rw [pop_byte, pop_byte, pop_byte, pop_byte]
  simp only [← Nat.shiftRight_add, Nat.mul_zero, Nat.shiftRight_zero, Nat.add_eq]
  norm_num
  ring

theorem testBit_foldr (sel : ℕ → ℕ) (RL : List ℕ) (X : Finset ℕ) {v : ℕ} (hv : v < 32)
    (l : List ℕ) :
    (l.foldr (fun a acc => if a ∈ X then Nat.land (sel (recAt RL a)) acc else acc)
        4294967295).testBit v = true ↔
      ∀ a ∈ l, a ∈ X → (sel (recAt RL a)).testBit v = true := by
  induction l with
  | nil =>
    have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
    simp only [List.foldr_nil, h32, Nat.testBit_two_pow_sub_one, decide_eq_true_eq, hv,
      List.not_mem_nil, false_imp_iff, implies_true]
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    split_ifs with ha
    · rw [land_eq, Nat.testBit_and, Bool.and_eq_true, ih]
      tauto
    · rw [ih]
      tauto

theorem testBit_andMask (sel : ℕ → ℕ) (RL : List ℕ) (X : Finset ℕ) {v : ℕ} (hv : v < 32) :
    (andMask sel RL X).testBit v ↔ ∀ a ∈ X, a < 191 → (sel (recAt RL a)).testBit v := by
  unfold andMask
  rw [testBit_foldr sel RL X hv]
  exact ⟨fun h a ha hl => h a (List.mem_range.2 hl) ha,
    fun h a hl ha => h a ha (List.mem_range.1 hl)⟩

theorem andMask_lt (sel : ℕ → ℕ) (RL : List ℕ) (X : Finset ℕ) : andMask sel RL X < 2 ^ 32 := by
  unfold andMask
  induction (List.range 191) with
  | nil => norm_num
  | cons a l ih =>
    simp only [List.foldr_cons]
    split_ifs
    · rw [land_eq]
      exact lt_of_le_of_lt Nat.and_le_right ih
    · exact ih

theorem testBit_of_range {p k : ℕ} (h1 : 2 ^ k ≤ p) (h2 : p < 2 ^ (k + 1)) :
    p.testBit k = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : p / 2 ^ k = 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [one_mul]
      exact h1
    · rw [pow_succ] at h2
      linarith
  simp [h]

def ofBitsF (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ofBitsF f n + if f n then 2 ^ n else 0

theorem ofBitsF_lt (f : ℕ → Bool) (n : ℕ) : ofBitsF f n < 2 ^ n := by
  induction n with
  | zero => simp [ofBitsF]
  | succ n ih =>
    simp only [ofBitsF, pow_succ]
    split_ifs <;> omega

theorem testBit_ofBitsF (f : ℕ → Bool) (n i : ℕ) :
    (ofBitsF f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [ofBitsF]
  | succ n ih =>
    have hl := ofBitsF_lt f n
    simp only [ofBitsF]
    split_ifs with hf
    · rw [Nat.add_comm]
      rcases lt_trichotomy i n with h | rfl | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        simp [h, Nat.lt_succ_of_lt h]
      · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hl]
        simp [hf]
      · have h' : 2 ^ n + ofBitsF f n < 2 ^ i := by
          have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt h)
          rw [pow_succ] at this
          omega
        rw [Nat.testBit_lt_two_pow h']
        simp
        omega
    · rw [Nat.add_zero, ih]
      rcases lt_or_ge i n with h | h
      · simp [h, Nat.lt_succ_of_lt h]
      · rcases Nat.eq_or_lt_of_le h with rfl | h2
        · simp [hf]
        · have h3 : ¬ i < n := by omega
          have h4 : ¬ i < n + 1 := by omega
          simp [h3, h4]

def spr (c : ℕ) : ℕ := ofBitsF (fun n => decide (n % 5 = 0) && c.testBit (n / 5)) 21

theorem spr_mul : ∀ c < 32, ∀ r < 32, ∀ i < 5, ∀ j < 5,
    (spr c * r).testBit (5 * i + j) = (c.testBit i && r.testBit j) := by
  decide +kernel

theorem spr_eq (A k : ℕ) :
    (A >>> k) &&& 1082401 = spr (ofBitsF (fun i => A.testBit (5 * i + k)) 5) := by
  have h1082 : (1082401 : ℕ) = spr 31 := by decide +kernel
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h1082, spr, spr, testBit_ofBitsF, testBit_ofBitsF,
    testBit_ofBitsF]
  have h31 : (31 : ℕ) = 2 ^ 5 - 1 := rfl
  rw [h31, Nat.testBit_two_pow_sub_one]
  by_cases hn : n < 21
  · by_cases h5 : n % 5 = 0
    · have hd : n / 5 < 5 := by omega
      have he : 5 * (n / 5) + k = k + n := by omega
      simp [hn, h5, hd, he]
    · simp [h5]
  · simp [hn]

theorem termBit (A B k i j : ℕ) (hk : k < 5) (hi : i < 5) (hj : j < 5) :
    (((A >>> k) &&& 1082401) * ((B >>> (5 * k)) &&& 31)).testBit (5 * i + j) =
      (A.testBit (5 * i + k) && B.testBit (5 * k + j)) := by
  have h31 : (31 : ℕ) = 2 ^ 5 - 1 := rfl
  have hr : (B >>> (5 * k)) &&& 31 < 32 := by
    rw [h31, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  rw [spr_eq, spr_mul _ (ofBitsF_lt _ 5) _ hr i hi j hj, testBit_ofBitsF, h31, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  simp [hi, hj]

theorem ite_xor5 : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    (if ((((a0 && b0) ^^ (a1 && b1)) ^^ (a2 && b2)) ^^ (a3 && b3)) ^^ (a4 && b4) = true
      then (1 : ZMod 2) else 0) =
    (if a0 = true then 1 else 0) * (if b0 = true then 1 else 0) +
      (if a1 = true then 1 else 0) * (if b1 = true then 1 else 0) +
      (if a2 = true then 1 else 0) * (if b2 = true then 1 else 0) +
      (if a3 = true then 1 else 0) * (if b3 = true then 1 else 0) +
      (if a4 = true then 1 else 0) * (if b4 = true then 1 else 0) := by
  decide

theorem mul25_spec' {A B : ℕ} :
    matOf (mul25 A B) = matOf A * matOf B := by
  have hT : mul25 A B = (((((0 ^^^ ((A >>> 0) &&& 1082401) * ((B >>> (5 * 0)) &&& 31)) ^^^
      ((A >>> 1) &&& 1082401) * ((B >>> (5 * 1)) &&& 31)) ^^^
      ((A >>> 2) &&& 1082401) * ((B >>> (5 * 2)) &&& 31)) ^^^
      ((A >>> 3) &&& 1082401) * ((B >>> (5 * 3)) &&& 31)) ^^^
      ((A >>> 4) &&& 1082401) * ((B >>> (5 * 4)) &&& 31)) := rfl
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [matOf, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_five, hT, Nat.testBit_xor,
    Nat.zero_testBit, Bool.false_xor]
  rw [termBit A B 0 i j (by omega) (by omega) (by omega), termBit A B 1 i j (by omega) (by omega)
    (by omega), termBit A B 2 i j (by omega) (by omega) (by omega), termBit A B 3 i j (by omega)
    (by omega) (by omega), termBit A B 4 i j (by omega) (by omega) (by omega)]
  exact ite_xor5 _ _ _ _ _ _ _ _ _ _

theorem rec_zero_N (b : ℕ) (s : ℕ → ℕ → ℕ) : (Nat.rec (motive := fun _ => ℕ) b s 0 : ℕ) = b := rfl

theorem coord_inv (k j p : ℕ) :
    (Nat.rec (motive := fun _ => Nat)
      (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 k)) 1) (Nat.shiftLeft 1 k))
      (fun j acc => letN acc fun a =>
        Nat.lor a (Nat.shiftLeft a (Nat.shiftLeft 1 (Nat.add (Nat.add k 1) j)))) j : ℕ).testBit p =
      (decide (p < 2 ^ (k + 1 + j)) && p.testBit k) := by
  induction j generalizing p with
  | zero =>
    have e : Nat.shiftLeft 1 k = 2 ^ k := by rw [shl_eq, Nat.shiftLeft_eq, one_mul]
    rw [rec_zero_N, e, shl_eq (Nat.sub (Nat.shiftLeft 1 (2 ^ k)) 1) (2 ^ k), Nat.shiftLeft_eq,
      Nat.testBit_mul_two_pow, testBit_mask, Nat.add_zero]
    by_cases h1 : 2 ^ k ≤ p
    · by_cases h2 : p < 2 ^ (k + 1)
      · have h3 : p - 2 ^ k < 2 ^ k := by
          rw [pow_succ] at h2
          omega
        simp [h1, h2, h3, testBit_of_range h1 h2]
      · have h3 : ¬ p - 2 ^ k < 2 ^ k := by
          rw [pow_succ] at h2
          omega
        simp [h1, h2, h3]
    · have h2 : p < 2 ^ (k + 1) := by
        rw [pow_succ]
        omega
      simp [h1, h2, Nat.testBit_lt_two_pow (lt_of_not_ge h1)]
  | succ j ih =>
    have e : Nat.shiftLeft 1 (Nat.add (Nat.add k 1) j) = 2 ^ (k + 1 + j) := by
      rw [shl_eq, Nat.shiftLeft_eq, one_mul]
      rfl
    change (letN (Nat.rec (motive := fun _ => ℕ) _ _ j) _).testBit p = _
    rw [letN_eq, e, lor_eq, Nat.testBit_or, shl_eq _ (2 ^ (k + 1 + j)), Nat.shiftLeft_eq, Nat.testBit_mul_two_pow, ih, ih]
    have hM : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [hM]
    by_cases h1 : 2 ^ (k + 1 + j) ≤ p
    · have hk : (p - 2 ^ (k + 1 + j)).testBit k = p.testBit k := by
        have hp : p = 2 ^ (k + 1 + j) + (p - 2 ^ (k + 1 + j)) := by omega
        conv_rhs => rw [hp]
        rw [Nat.testBit_two_pow_add_gt (by omega)]
      have h3 : p - 2 ^ (k + 1 + j) < 2 ^ (k + 1 + j) ↔ p < 2 ^ (k + 1 + j + 1) := by
        rw [pow_succ]
        omega
      have h4 : ¬ p < 2 ^ (k + 1 + j) := by omega
      simp only [hk, h1, h4, decide_false, Bool.false_and, Bool.false_or, decide_true,
        Bool.true_and]
      by_cases h5 : p < 2 ^ (k + 1 + j + 1)
      · simp [h5, h3.2 h5]
      · simp [h5, mt h3.1 h5]
    · have h4 : p < 2 ^ (k + 1 + j) := by omega
      have h5 : p < 2 ^ (k + 1 + j + 1) := by
        rw [pow_succ]
        omega
      simp [h1, h4, h5]

theorem coord_testBit {k p : ℕ} (hk : k < 15) (hp : p < 2 ^ 15) :
    (coord k).testBit p = p.testBit k := by
  unfold coord
  rw [coord_inv, Nat.sub_eq]
  have h : k + 1 + (14 - k) = 15 := by omega
  rw [h]
  have hp' : p < 32768 := lt_of_lt_of_le hp (by norm_num)
  simp [hp']

def xorL (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => xorL f n ^^ f n

@[expose] noncomputable def xrec (g : ℕ → ℕ) (b : ℕ → Bool) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (coord (g j))) (b j)) n

theorem testBit_xrec (g : ℕ → ℕ) (b : ℕ → Bool) {p : ℕ} (hp : p < 2 ^ 15) (n : ℕ)
    (hg : ∀ j < n, g j < 15) :
    (xrec g b n).testBit p = xorL (fun j => b j && p.testBit (g j)) n := by
  induction n with
  | zero => simp [xrec, xorL]
  | succ n ih =>
    have hs : xrec g b (n + 1) =
        Bool.rec (motive := fun _ => ℕ) (xrec g b n) (Nat.xor (xrec g b n) (coord (g n))) (b n) :=
      rfl
    rw [hs, xorL, ← ih (fun j hj => hg j (by omega))]
    cases b n
    · simp
    · rw [xor_eq, Nat.testBit_xor, coord_testBit (hg n (by omega)) hp]
      simp

theorem rowZ_eq (v i : ℕ) :
    rowZ v i = xrec (fun j => fd 4 symIdx (Nat.add (Nat.mul 5 i) j)) (fun j => bitB v j) 5 := rfl

@[expose] noncomputable def zrec (v n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) full
    (fun i acc => letN acc fun a => Nat.land a (Nat.xor full (rowZ v i))) n

theorem testBit_zrec (v : ℕ) {p : ℕ} (hp : p < 32768) (n : ℕ) :
    (zrec v n).testBit p = true ↔ ∀ i < n, (rowZ v i).testBit p = false := by
  induction n with
  | zero =>
    change full.testBit p = true ↔ _
    simp [testBit_full, hp]
  | succ n ih =>
    have hs : zrec v (n + 1) = Nat.land (zrec v n) (Nat.xor full (rowZ v n)) := by
      change letN (zrec v n) (fun a => Nat.land a (Nat.xor full (rowZ v n))) = _
      rw [letN_eq]
    rw [hs, land_eq, xor_eq, Nat.testBit_and, Nat.testBit_xor, testBit_full, Bool.and_eq_true, ih]
    simp only [hp, decide_true, Bool.true_xor, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem zMask_eq (v : ℕ) : zMask v = zrec v 5 := rfl

@[expose] noncomputable def srec (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun v acc => letN acc fun a => Nat.lor a (zMask (Nat.succ v))) n

theorem testBit_srec (p n : ℕ) :
    (srec n).testBit p = true ↔ ∃ w < n, (zMask (w + 1)).testBit p = true := by
  induction n with
  | zero => simp [srec]
  | succ n ih =>
    have hs : srec (n + 1) = Nat.lor (srec n) (zMask (n + 1)) := by
      change letN (srec n) (fun a => Nat.lor a (zMask (Nat.succ n))) = _
      rw [letN_eq]
    rw [hs, lor_eq, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨w, hw, h⟩ | h)
      · exact ⟨w, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨w, hw, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h' | rfl
      · exact Or.inl ⟨w, h', h⟩
      · exact Or.inr h

theorem symIdx_lt : ∀ i < 5, ∀ j < 5, fd 4 symIdx (Nat.add (Nat.mul 5 i) j) < 15 := by
  decide +kernel

theorem ite_xor5' : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    (if (((((false ^^ (b0 && a0)) ^^ (b1 && a1)) ^^ (b2 && a2)) ^^ (b3 && a3)) ^^ (b4 && a4)) = true
      then (1 : ZMod 2) else 0) =
    (if a0 = true then 1 else 0) * (if b0 = true then 1 else 0) +
      (if a1 = true then 1 else 0) * (if b1 = true then 1 else 0) +
      (if a2 = true then 1 else 0) * (if b2 = true then 1 else 0) +
      (if a3 = true then 1 else 0) * (if b3 = true then 1 else 0) +
      (if a4 = true then 1 else 0) * (if b4 = true then 1 else 0) := by
  decide

theorem row_eq {p : ℕ} (hp : p < 2 ^ 15) (v : ℕ) (i : Fin 5) :
    (symC p *ᵥ vdec v) i = if (rowZ v i).testBit p then 1 else 0 := by
  rw [rowZ_eq, testBit_xrec _ _ hp 5 (fun j hj => symIdx_lt i i.2 j hj)]
  simp only [xorL, bitB_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_five, symC, Matrix.of_apply,
    vdec, Nat.add_eq, Nat.mul_eq]
  exact (ite_xor5' _ _ _ _ _ _ _ _ _ _).symm

theorem testBit_bit1 (P a m : ℕ) :
    ((P >>> a) &&& 1).testBit m = (decide (m = 0) && P.testBit a) := by
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  cases m with
  | zero => simp
  | succ m =>
    have h : (1 : ℕ).testBit (m + 1) = false := by
      rw [← Bool.not_eq_true, Nat.testBit_one_eq_true_iff_self_eq_zero]
      omega
    simp [h]

@[expose] noncomputable def encRec (P n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc
    (Nat.shiftLeft (Nat.land (Nat.shiftRight P (fd 5 symPos k)) 1) k)) n

theorem testBit_symEncRec (P j n : ℕ) :
    (encRec P n).testBit j = (decide (j < n) && P.testBit (fd 5 symPos j)) := by
  induction n with
  | zero => simp [encRec]
  | succ n ih =>
    have hs : encRec P (n + 1) = Nat.lor (encRec P n)
        (Nat.shiftLeft (Nat.land (Nat.shiftRight P (fd 5 symPos n)) 1) n) := rfl
    rw [hs, lor_eq, Nat.testBit_or, ih, shl_eq, Nat.testBit_shiftLeft, land_eq, shr_eq,
      testBit_bit1]
    by_cases h : j < n
    · have h1 : j < n + 1 := by omega
      have h2 : ¬ (j ≥ n) := by omega
      simp [h, h1, h2]
    · by_cases h' : j = n
      · subst h'
        simp
      · have h1 : ¬ j < n + 1 := by omega
        have h3 : j - n ≠ 0 := by omega
        simp [h, h1, h3]

theorem testBit_symEnc25 (P j : ℕ) :
    (symEnc25 P).testBit j = (decide (j < 15) && P.testBit (fd 5 symPos j)) :=
  testBit_symEncRec P j 15

@[expose] noncomputable def trRec (A n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.lor acc
    (Nat.shiftLeft (Nat.land (Nat.shiftRight A t) 1)
      (Nat.add (Nat.mul 5 (Nat.mod t 5)) (Nat.div t 5)))) n

theorem testBit_trRec (A q n : ℕ) :
    (trRec A n).testBit q = true ↔ ∃ t < n, 5 * (t % 5) + t / 5 = q ∧ A.testBit t = true := by
  induction n with
  | zero => simp [trRec]
  | succ n ih =>
    have e : Nat.add (Nat.mul 5 (Nat.mod n 5)) (Nat.div n 5) = 5 * (n % 5) + n / 5 := rfl
    have hs : trRec A (n + 1) = Nat.lor (trRec A n) (Nat.shiftLeft
        (Nat.land (Nat.shiftRight A n) 1) (Nat.add (Nat.mul 5 (Nat.mod n 5)) (Nat.div n 5))) := rfl
    rw [hs, lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, shl_eq, e, Nat.testBit_shiftLeft,
      land_eq, shr_eq, testBit_bit1]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨t, ht, h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨t, by omega, h1, h2⟩
      · exact ⟨n, by omega, by omega, h3⟩
    · rintro ⟨t, ht, h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | rfl
      · exact Or.inl ⟨t, h, h1, h2⟩
      · exact Or.inr ⟨by omega, by omega, h2⟩

theorem testBit_tr25 (A q : ℕ) :
    (tr25 A).testBit q = true ↔ ∃ t < 25, 5 * (t % 5) + t / 5 = q ∧ A.testBit t = true :=
  testBit_trRec A q 25

theorem matOf_tr25 (A : ℕ) : matOf (tr25 A) = (matOf A)ᵀ := by
  ext i j
  have hi := i.2
  have hj := j.2
  have h : (tr25 A).testBit (5 * (i : ℕ) + j) = A.testBit (5 * (j : ℕ) + i) := by
    rw [Bool.eq_iff_iff, testBit_tr25]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      have ht' : t = 5 * (j : ℕ) + i := by omega
      rw [← ht']
      exact h2
    · intro h
      exact ⟨5 * (j : ℕ) + i, by omega, by omega, h⟩
  simp only [matOf, Matrix.of_apply, Matrix.transpose_apply, h]

theorem symE_bits : ∀ k < 15, ∀ i < 5, ∀ j < 5,
    (symE k).testBit (5 * i + j) = (2 ^ k).testBit (fd 4 symIdx (5 * i + j)) := by
  decide +kernel

theorem matOf_symE {k : ℕ} (hk : k < 15) : matOf (symE k) = symC (2 ^ k) := by
  ext i j
  simp only [matOf, symC, Matrix.of_apply, symE_bits k hk i i.2 j j.2]

theorem xorL_ite (f : ℕ → Bool) (n : ℕ) :
    (if xorL f n then (1 : ZMod 2) else 0) = ∑ k ∈ Finset.range n, if f k then 1 else 0 := by
  induction n with
  | zero => simp [xorL]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, xorL]
    cases xorL f n <;> cases f n <;> decide

theorem symC_sum (p : ℕ) :
    symC p = ∑ k ∈ Finset.range 15, (if p.testBit k then (1 : ZMod 2) else 0) • symC (2 ^ k) := by
  ext i j
  have hl : fd 4 symIdx (5 * (i : ℕ) + j) < 15 := symIdx_lt i i.2 j j.2
  rw [Matrix.sum_apply]
  simp only [symC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Nat.testBit_two_pow]
  rw [Finset.sum_eq_single (fd 4 symIdx (5 * (i : ℕ) + j))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.2 hl) h

theorem planeOf_eq (M j : ℕ) :
    planeOf M j = xrec (fun k => k) (fun k => bitB (img M (tr25 M) k) j) 15 := by
  unfold planeOf
  rw [letN_eq]
  rfl

theorem ite_and2 (a b : Bool) : (if (a && b) = true then (1 : ZMod 2) else 0) =
    (if b = true then 1 else 0) * (if a = true then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem ite_inj2 {a b : Bool}
    (h : (if a = true then (1 : ZMod 2) else 0) = if b = true then 1 else 0) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem plane_spec (M : ℕ) {p j : ℕ} (hp : p < 2 ^ 15) (hj : j < 15) (r c : Fin 5)
    (hrc : 5 * (r : ℕ) + c = fd 5 symPos j) :
    (if (planeOf M j).testBit p then (1 : ZMod 2) else 0) =
      (matOf M * symC p * (matOf M)ᵀ) r c := by
  rw [planeOf_eq, testBit_xrec _ _ hp 15 (fun k hk => hk), xorL_ite, symC_sum p]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have hX : matOf M * symC (2 ^ k) * (matOf M)ᵀ = matOf (mul25 (mul25 M (symE k)) (tr25 M)) := by
    rw [mul25_spec', mul25_spec', matOf_tr25, matOf_symE hk']
  have hb : bitB (img M (tr25 M) k) j =
      (mul25 (mul25 M (symE k)) (tr25 M)).testBit (5 * (r : ℕ) + c) := by
    rw [bitB_eq, hrc, img, testBit_symEnc25]
    simp [hj]
  rw [hX, hb, ite_and2]
  rfl

theorem ffG_spec {M p : ℕ} (_hM : M < 2 ^ 25) (hp : p < 2 ^ 15) :
    (ffG M).testBit p ↔ matOf M * symC p * (matOf M)ᵀ = symC p := by
  have hp' : p < 32768 := lt_of_lt_of_le hp (by norm_num)
  have h1 : (ffG M).testBit p = true ↔ ∀ j < 15, (planeOf M j).testBit p = p.testBit j := by
    have hR : ∀ n, (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => letN acc fun a =>
        Nat.lor a (Nat.xor (planeOf M j) (coord j))) n : ℕ).testBit p = true ↔
        ∃ j < n, (planeOf M j).testBit p ≠ (coord j).testBit p := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        change (letN (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => letN acc fun a =>
          Nat.lor a (Nat.xor (planeOf M j) (coord j))) n) _).testBit p = true ↔ _
        rw [letN_eq, lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, xor_eq,
          Nat.testBit_xor]
        constructor
        · rintro (⟨j, hj, h⟩ | h)
          · exact ⟨j, by omega, h⟩
          · refine ⟨n, by omega, ?_⟩
            revert h
            cases (planeOf M n).testBit p <;> cases (coord n).testBit p <;> simp
        · rintro ⟨j, hj, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
          · exact Or.inl ⟨j, h', h⟩
          · right
            revert h
            cases (planeOf M j).testBit p <;> cases (coord j).testBit p <;> simp
    change (Nat.xor full _).testBit p = true ↔ _
    rw [xor_eq, Nat.testBit_xor, testBit_full]
    simp only [hp', decide_true, Bool.true_xor, Bool.not_eq_true']
    rw [← Bool.not_eq_true, hR]
    push Not
    refine forall₂_congr fun j hj => ?_
    rw [coord_testBit hj hp]
  have hpos : ∀ j < 15, fd 5 symPos j < 25 ∧ fd 4 symIdx (fd 5 symPos j) = j := by
    decide +kernel
  have hs : ∀ i j : Fin 5, fd 4 symIdx (5 * (i : ℕ) + j) < 15 ∧
      fd 5 symPos (fd 4 symIdx (5 * (i : ℕ) + j)) = 5 * min (i : ℕ) j + max (i : ℕ) j := by
    decide +kernel
  have hsymm : ∀ i j : Fin 5, fd 4 symIdx (5 * (i : ℕ) + j) = fd 4 symIdx (5 * (j : ℕ) + i) := by
    decide +kernel
  have hS : (symC p)ᵀ = symC p := by
    ext i j
    simp only [symC, Matrix.transpose_apply, Matrix.of_apply, hsymm j i]
  have hQ : (matOf M * symC p * (matOf M)ᵀ)ᵀ = matOf M * symC p * (matOf M)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS,
      Matrix.mul_assoc]
  rw [h1]
  constructor
  · intro h
    have key : ∀ i j : Fin 5, (i : ℕ) ≤ j →
        (matOf M * symC p * (matOf M)ᵀ) i j = symC p i j := by
      intro i j hij
      obtain ⟨hk, hpk⟩ := hs i j
      rw [min_eq_left hij, max_eq_right hij] at hpk
      rw [← plane_spec M hp hk i j hpk.symm, h _ hk]
      rfl
    ext i j
    rcases le_total (i : ℕ) j with hij | hij
    · exact key i j hij
    · rw [← hQ, ← hS, Matrix.transpose_apply, Matrix.transpose_apply]
      exact key j i hij
  · intro h j hj
    obtain ⟨h25, hidx⟩ := hpos j hj
    have hrc : 5 * ((⟨fd 5 symPos j / 5, by omega⟩ : Fin 5) : ℕ) +
        ((⟨fd 5 symPos j % 5, by omega⟩ : Fin 5) : ℕ) = fd 5 symPos j := by
      simp only
      omega
    apply ite_inj2
    rw [plane_spec M hp hj _ _ hrc, h]
    simp only [symC, Matrix.of_apply, hrc, hidx]

theorem allN_spec (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    have hs : allN (n + 1) f = andB (f n) (allN n f) := rfl
    rw [hs, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem testBit_I : ∀ i < 5, ∀ j < 5, (17043521 : ℕ).testBit (5 * i + j) = decide (i = j) := by
  decide +kernel

theorem matOf_one : matOf 17043521 = 1 := by
  ext i j
  simp only [matOf, Matrix.of_apply, Matrix.one_apply, testBit_I i i.2 j j.2, decide_eq_true_eq,
    Fin.val_inj]

theorem matOf_inj {a b : ℕ} (ha : a < 2 ^ 25) (hb : b < 2 ^ 25) (h : matOf a = matOf b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < 25
  · have h1 := congrFun (congrFun h ⟨q / 5, by omega⟩) ⟨q % 5, by omega⟩
    simp only [matOf, Matrix.of_apply, Fin.val_mk] at h1
    have e : 5 * (q / 5) + q % 5 = q := by omega
    rw [e] at h1
    exact ite_inj2 h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] noncomputable def repN (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun L acc => acc + 2 ^ (25 * L)) n

theorem repN_succ (n : ℕ) : repN (n + 1) = repN n + 2 ^ (25 * n) := rfl

theorem repU_eq : repU = repN 191 := by decide +kernel

theorem mulRep_lt {U : ℕ} (hU : U < 2 ^ 25) (n : ℕ) : U * repN n < 2 ^ (25 * n) := by
  induction n with
  | zero => simp [repN]
  | succ n ih =>
    have hP : U * 2 ^ (25 * n) + 2 ^ (25 * n) ≤ 2 ^ 25 * 2 ^ (25 * n) := by
      have h := Nat.mul_le_mul_right (2 ^ (25 * n)) (Nat.succ_le_of_lt hU)
      rw [Nat.succ_mul] at h
      exact h
    have e : 25 * (n + 1) = 25 * n + 25 := by ring
    rw [repN_succ, Nat.mul_add, e, pow_add]
    linarith

theorem testBit_mulRep {U : ℕ} (hU : U < 2 ^ 25) (n q : ℕ) :
    (U * repN n).testBit q = (decide (q < 25 * n) && U.testBit (q % 25)) := by
  induction n with
  | zero => simp [repN]
  | succ n ih =>
    have e : U * repN (n + 1) = 2 ^ (25 * n) * U + U * repN n := by
      rw [repN_succ]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ (mulRep_lt hU n), ih]
    split_ifs with h
    · have h' : q < 25 * (n + 1) := by omega
      simp [h, h']
    · by_cases h2 : q < 25 * (n + 1)
      · have e2 : q - 25 * n = q % 25 := by omega
        simp [h2, e2]
      · have hq : U < 2 ^ (q - 25 * n) :=
          lt_of_lt_of_le hU (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [h2, Nat.testBit_lt_two_pow hq]

theorem testBit_one' (i : ℕ) : (1 : ℕ).testBit i = decide (i = 0) := by
  rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_iff]

theorem testBit_repU (q : ℕ) : repU.testBit q = (decide (q < 4775) && decide (q % 25 = 0)) := by
  rw [repU_eq, ← one_mul (repN 191), testBit_mulRep (by norm_num) 191 q, testBit_one']

theorem testBit_orShr (a s q : ℕ) :
    (Nat.lor a (Nat.shiftRight a s)).testBit q = (a.testBit q || a.testBit (s + q)) := by
  rw [lor_eq, shr_eq, Nat.testBit_or, Nat.testBit_shiftRight]

theorem win_step {t a k s : ℕ} (hs : s ≤ k)
    (ha : ∀ q, a.testBit q = true ↔ ∃ d < k, t.testBit (q + d) = true) :
    ∀ q, (Nat.lor a (Nat.shiftRight a s)).testBit q = true ↔
      ∃ d < k + s, t.testBit (q + d) = true := by
  intro q
  rw [testBit_orShr, Bool.or_eq_true, ha, ha]
  constructor
  · rintro (⟨d, hd, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨d, by omega, h⟩
    · have e : s + q + d = q + (s + d) := by omega
      rw [e] at h
      exact ⟨s + d, by omega, h⟩
  · rintro ⟨d, hd, h⟩
    by_cases hdk : d < k
    · exact Or.inl ⟨d, hdk, h⟩
    · refine Or.inr ⟨d - s, by omega, ?_⟩
      have e : s + q + (d - s) = q + d := by omega
      rw [e]
      exact h

theorem testBit_fold25 (t q : ℕ) :
    (fold25 t).testBit q = true ↔ ∃ d < 25, t.testBit (q + d) = true := by
  have h1 : ∀ q, t.testBit q = true ↔ ∃ d < 1, t.testBit (q + d) = true := by
    intro q
    constructor
    · intro h
      exact ⟨0, by omega, h⟩
    · rintro ⟨d, hd, h⟩
      have hd0 : d = 0 := by omega
      subst hd0
      exact h
  have h2 := win_step (s := 1) (by omega) h1
  have h4 := win_step (s := 2) (by omega) h2
  have h8 := win_step (s := 4) (by omega) h4
  have h16 := win_step (s := 8) (by omega) h8
  have h25 := win_step (s := 9) (by omega) h16
  unfold fold25
  simp only [letN_eq]
  exact h25 q

@[expose] noncomputable def uniRec (c n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 17043521
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight c k) 1) (fd 5 upBits k))) n

theorem testBit_uniRec (c q n : ℕ) :
    (uniRec c n).testBit q = true ↔
      (17043521 : ℕ).testBit q = true ∨ ∃ k < n, fd 5 upBits k = q ∧ c.testBit k = true := by
  induction n with
  | zero => simp [uniRec]
  | succ n ih =>
    have hs : uniRec c (n + 1) = Nat.lor (uniRec c n)
        (Nat.shiftLeft (Nat.land (Nat.shiftRight c n) 1) (fd 5 upBits n)) := rfl
    rw [hs, lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, shl_eq, Nat.testBit_shiftLeft, land_eq,
      shr_eq, testBit_bit1]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | ⟨k, hk, h1, h2⟩) | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, h1, h2⟩
      · exact Or.inr ⟨n, by omega, by omega, h3⟩
    · rintro (h | ⟨k, hk, h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
        · exact Or.inl (Or.inr ⟨k, h, h1, h2⟩)
        · exact Or.inr ⟨by omega, by omega, h2⟩

theorem uni_eq (c : ℕ) : uni c = uniRec c 10 := rfl

theorem exists_uni (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hu : IsUni M) :
    ∃ c < 1024, matOf (uni c) = M := by
  let P' : ℕ → ℕ → ZMod 2 := fun a b => if h : a < 5 ∧ b < 5 then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  let f : ℕ → Bool := fun k => decide (P' (fd 5 upBits k / 5) (fd 5 upBits k % 5) = 1)
  refine ⟨ofBitsF f 10, ofBitsF_lt f 10, ?_⟩
  have hpos : ∀ k < 10, fd 5 upBits k < 25 ∧ fd 5 upBits k / 5 < fd 5 upBits k % 5 := by
    decide +kernel
  have hinv : ∀ i < 5, ∀ j < 5, i < j → ∃ k < 10, fd 5 upBits k = 5 * i + j := by
    decide +kernel
  have hinj : ∀ k < 10, ∀ k' < 10, fd 5 upBits k = fd 5 upBits k' → k = k' := by
    decide +kernel
  have hz : ∀ x : ZMod 2, (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by decide
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [matOf, Matrix.of_apply]
  rw [uni_eq]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · obtain ⟨k, hk, hkp⟩ := hinv i hi j hj h
    have hk' : (ofBitsF f 10).testBit k = f k := by
      rw [testBit_ofBitsF]
      simp [hk]
    have hb : (uniRec (ofBitsF f 10) 10).testBit (5 * (i : ℕ) + j) = f k := by
      rw [Bool.eq_iff_iff, testBit_uniRec, testBit_I i hi j hj]
      constructor
      · rintro (h0 | ⟨k', hk2, h1, h2⟩)
        · simp only [decide_eq_true_eq] at h0
          omega
        · have hkk : k' = k := hinj k' hk2 k hk (h1.trans hkp.symm)
          subst hkk
          rw [← hk']
          exact h2
      · intro hf
        exact Or.inr ⟨k, hk, hkp, by rw [hk']; exact hf⟩
    rw [hb]
    have hd : (5 * (i : ℕ) + j) / 5 = i := by omega
    have hm : (5 * (i : ℕ) + j) % 5 = j := by omega
    simp only [f, hkp, hd, hm, P', hi, hj, and_self, dite_true, Fin.eta]
    exact hz _
  · have hij : i = j := Fin.ext h
    subst hij
    have hb : (uniRec (ofBitsF f 10) 10).testBit (5 * (i : ℕ) + i) = true :=
      (testBit_uniRec _ _ _).2 (Or.inl (by rw [testBit_I i hi i hi]; simp))
    rw [hb, hu.2 i]
    rfl
  · have hb : (uniRec (ofBitsF f 10) 10).testBit (5 * (i : ℕ) + j) = false := by
      rw [Bool.eq_false_iff]
      intro hb
      rcases (testBit_uniRec _ _ _).1 hb with h0 | ⟨k, hk, h1, -⟩
      · rw [testBit_I i hi j hj] at h0
        simp only [decide_eq_true_eq] at h0
        omega
      · have := hpos k hk
        omega
    rw [hb, hu.1 i j h]
    rfl

theorem complOK_sound {MT : ℕ} (h : complOK MT = true) (M : Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hu : IsUni M) (h2 : M * M = 1) (h1 : M ≠ 1) : ∃ i < 191, matOf (lane MT i) = M := by
  obtain ⟨c, hc, hcM⟩ := exists_uni M hu
  have huni : ∀ c < 1024, uni c < 2 ^ 25 ∧ mul25 (uni c) (uni c) < 2 ^ 25 := by decide +kernel
  obtain ⟨hU, hUU⟩ := huni c hc
  have hck := (allN_spec 1024 _).1 h c hc
  simp only [letB_eq, orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at hck
  rcases hck with hm | hm | hm
  · have hX : mul25 (uni c) (uni c) = 17043521 :=
      matOf_inj hUU (by norm_num) (by rw [mul25_spec', hcM, h2, matOf_one])
    rw [hX, Nat.beq_refl] at hm
    exact absurd hm (by decide)
  · have he := Nat.eq_of_beq_eq_true hm
    rw [he, matOf_one] at hcM
    exact absurd hcM.symm h1
  · by_contra hne
    push Not at hne
    have ht : ∀ q, (Nat.xor MT (Nat.mul (uni c) repU)).testBit q =
        (MT.testBit q ^^ (decide (q < 4775) && (uni c).testBit (q % 25))) := by
      intro q
      change (MT ^^^ uni c * repU).testBit q = _
      rw [Nat.testBit_xor, repU_eq, testBit_mulRep hU 191 q]
    suffices hs : Nat.land (fold25 (Nat.xor MT (Nat.mul (uni c) repU))) repU = repU by
      rw [hs, Nat.beq_refl] at hm
      exact absurd hm (by decide)
    apply Nat.eq_of_testBit_eq
    intro q
    rw [land_eq, Nat.testBit_and, testBit_repU]
    by_cases hq : q < 4775 ∧ q % 25 = 0
    · obtain ⟨hq1, hq2⟩ := hq
      simp only [hq1, hq2, decide_true, Bool.and_true]
      by_contra hf
      rw [testBit_fold25] at hf
      push Not at hf
      apply hne (q / 25) (by omega)
      rw [← hcM]
      congr 1
      apply Nat.eq_of_testBit_eq
      intro d
      rw [lane, fd_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      by_cases hd : d < 25
      · have hfd := hf d hd
        rw [ht] at hfd
        have e1 : (q + d) % 25 = d := by omega
        have e2 : q + d < 4775 := by omega
        have e3 : 25 * (q / 25) + d = q + d := by omega
        simp only [e1, e2, e3, decide_true, Bool.true_and, hd] at hfd ⊢
        revert hfd
        cases MT.testBit (q + d) <;> cases (uni c).testBit d <;> simp
      · have hlt : uni c < 2 ^ d :=
          lt_of_lt_of_le hU (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [hd, Nat.testBit_lt_two_pow hlt]
    · have hf : (decide (q < 4775) && decide (q % 25 = 0)) = false := by
        rw [Bool.eq_false_iff]
        intro h'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
        exact hq h'
      rw [hf, Bool.and_false]

theorem fd25_testBit (X z d : ℕ) :
    (fd 25 X z).testBit d = (decide (d < 25) && X.testBit (25 * z + d)) := by
  rw [fd_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem fd25_lt (X z : ℕ) : fd 25 X z < 2 ^ 25 := by
  rw [fd_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem fd25_xor (a b z : ℕ) : fd 25 (a ^^^ b) z = fd 25 a z ^^^ fd 25 b z := by
  apply Nat.eq_of_testBit_eq
  intro d
  simp only [fd25_testBit, Nat.testBit_xor]
  cases decide (d < 25) <;> simp

theorem div_lane (A X : ℕ) (h0 : A * (X % 2 ^ 25) < 2 ^ 25) :
    A * X % 2 ^ 25 = A * (X % 2 ^ 25) ∧ A * X / 2 ^ 25 = A * (X / 2 ^ 25) := by
  have e : A * X = A * (X % 2 ^ 25) + 2 ^ 25 * (A * (X / 2 ^ 25)) := by
    conv_lhs => rw [← Nat.mod_add_div X (2 ^ 25)]
    ring
  constructor
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  · rw [e, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h0, Nat.zero_add]

theorem fd25_succ (Y z : ℕ) : fd 25 Y (z + 1) = fd 25 (Y / 2 ^ 25) z := by
  have e : 25 * (z + 1) = 25 + 25 * z := by ring
  rw [fd_eq, fd_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← pow_add, e]

theorem fd25_zero (Y : ℕ) : fd 25 Y 0 = Y % 2 ^ 25 := by
  rw [fd_eq, Nat.mul_zero, Nat.shiftRight_zero]

theorem lane_mul (A z : ℕ) : ∀ X, (∀ y, A * fd 25 X y < 2 ^ 25) →
    fd 25 (A * X) z = A * fd 25 X z := by
  induction z with
  | zero =>
    intro X hX
    have h0 := hX 0
    rw [fd25_zero] at h0
    rw [fd25_zero, fd25_zero]
    exact (div_lane A X h0).1
  | succ z ih =>
    intro X hX
    have h0 := hX 0
    rw [fd25_zero] at h0
    rw [fd25_succ, fd25_succ, (div_lane A X h0).2]
    apply ih
    intro y
    rw [← fd25_succ]
    exact hX (y + 1)

theorem testBit_mulRepU {c : ℕ} (hc : c < 2 ^ 25) (q : ℕ) :
    (c * repU).testBit q = (decide (q < 4775) && c.testBit (q % 25)) := by
  rw [repU_eq, testBit_mulRep hc 191 q]

theorem fd25_and_rep {c : ℕ} (hc : c < 2 ^ 25) (Y z : ℕ) :
    fd 25 (Y &&& c * repU) z = if z < 191 then fd 25 Y z &&& c else 0 := by
  apply Nat.eq_of_testBit_eq
  intro d
  rw [fd25_testBit, Nat.testBit_and, testBit_mulRepU hc]
  split_ifs with hz
  · rw [Nat.testBit_and, fd25_testBit]
    by_cases hd : d < 25
    · have e1 : 25 * z + d < 4775 := by omega
      have e2 : (25 * z + d) % 25 = d := by omega
      simp only [hd, e1, e2, decide_true, Bool.true_and]
    · simp [hd]
  · have e1 : ¬ 25 * z + d < 4775 := by omega
    simp [e1]

theorem fd25_shr_and {k m : ℕ} (hm : m < 2 ^ (25 - k)) (Y z : ℕ) :
    fd 25 (Y >>> k) z &&& m = (fd 25 Y z >>> k) &&& m := by
  apply Nat.eq_of_testBit_eq
  intro d
  rw [Nat.testBit_and, Nat.testBit_and, fd25_testBit, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, fd25_testBit]
  by_cases hd : k + d < 25
  · have hd' : d < 25 := by omega
    have e : k + (25 * z + d) = 25 * z + (k + d) := by omega
    simp only [hd, hd', e, decide_true, Bool.true_and]
  · have hm' : m.testBit d = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hm']

theorem spr_mul_lt : ∀ c < 32, ∀ r < 32, spr c * r < 2 ^ 25 := by
  decide +kernel

theorem spr_bound (A k r : ℕ) (hr : r < 32) : ((A >>> k) &&& 1082401) * r < 2 ^ 25 := by
  rw [spr_eq]
  exact spr_mul_lt _ (ofBitsF_lt _ 5) r hr

theorem and31_lt (x : ℕ) : x &&& 31 < 32 := Nat.lt_succ_of_le Nat.and_le_right

theorem fd25_prodL (M MT : ℕ) {z : ℕ} (hz : z < 191) :
    fd 25 (prodL M MT) z = mul25 M (fd 25 MT z) := by
  have hT : ∀ X, Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc
      (Nat.mul (Nat.land (Nat.shiftRight M k) 1082401) (Nat.land (Nat.shiftRight X (Nat.mul 5 k))
        (Nat.mul 31 repU)))) 5 =
      ((((0 ^^^ ((M >>> 0) &&& 1082401) * ((X >>> (5 * 0)) &&& 31 * repU)) ^^^
        ((M >>> 1) &&& 1082401) * ((X >>> (5 * 1)) &&& 31 * repU)) ^^^
        ((M >>> 2) &&& 1082401) * ((X >>> (5 * 2)) &&& 31 * repU)) ^^^
        ((M >>> 3) &&& 1082401) * ((X >>> (5 * 3)) &&& 31 * repU)) ^^^
        ((M >>> 4) &&& 1082401) * ((X >>> (5 * 4)) &&& 31 * repU) := fun _ => rfl
  have hM : mul25 M (fd 25 MT z) =
      ((((0 ^^^ ((M >>> 0) &&& 1082401) * ((fd 25 MT z >>> (5 * 0)) &&& 31)) ^^^
        ((M >>> 1) &&& 1082401) * ((fd 25 MT z >>> (5 * 1)) &&& 31)) ^^^
        ((M >>> 2) &&& 1082401) * ((fd 25 MT z >>> (5 * 2)) &&& 31)) ^^^
        ((M >>> 3) &&& 1082401) * ((fd 25 MT z >>> (5 * 3)) &&& 31)) ^^^
        ((M >>> 4) &&& 1082401) * ((fd 25 MT z >>> (5 * 4)) &&& 31) := rfl
  have hterm : ∀ k < 5, fd 25 (((M >>> k) &&& 1082401) * ((MT >>> (5 * k)) &&& 31 * repU)) z =
      ((M >>> k) &&& 1082401) * ((fd 25 MT z >>> (5 * k)) &&& 31) := by
    intro k hk
    have h31 : (31 : ℕ) < 2 ^ 25 := by norm_num
    rw [lane_mul]
    · rw [fd25_and_rep h31, if_pos hz, fd25_shr_and]
      exact lt_of_lt_of_le (by norm_num : (31 : ℕ) < 2 ^ 5)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro y
      rw [fd25_and_rep h31]
      split_ifs
      · exact spr_bound M k _ (and31_lt _)
      · rw [Nat.mul_zero]
        norm_num
  have h0 : fd 25 0 z = 0 := by
    rw [fd_eq, Nat.zero_shiftRight, Nat.zero_mod]
  unfold prodL
  rw [letN_eq, hT, hM, fd25_xor, fd25_xor, fd25_xor, fd25_xor, fd25_xor, h0,
    hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega),
    hterm 4 (by omega)]

theorem fd25_prodR (M MT : ℕ) {z : ℕ} (hz : z < 191) :
    fd 25 (prodR M MT) z = mul25 (fd 25 MT z) M := by
  have hT : ∀ X, Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc
      (Nat.mul (Nat.land (Nat.shiftRight X k) (Nat.mul 1082401 repU))
        (Nat.land (Nat.shiftRight M (Nat.mul 5 k)) 31))) 5 =
      ((((0 ^^^ ((X >>> 0) &&& 1082401 * repU) * ((M >>> (5 * 0)) &&& 31)) ^^^
        ((X >>> 1) &&& 1082401 * repU) * ((M >>> (5 * 1)) &&& 31)) ^^^
        ((X >>> 2) &&& 1082401 * repU) * ((M >>> (5 * 2)) &&& 31)) ^^^
        ((X >>> 3) &&& 1082401 * repU) * ((M >>> (5 * 3)) &&& 31)) ^^^
        ((X >>> 4) &&& 1082401 * repU) * ((M >>> (5 * 4)) &&& 31) := fun _ => rfl
  have hM : mul25 (fd 25 MT z) M =
      ((((0 ^^^ ((fd 25 MT z >>> 0) &&& 1082401) * ((M >>> (5 * 0)) &&& 31)) ^^^
        ((fd 25 MT z >>> 1) &&& 1082401) * ((M >>> (5 * 1)) &&& 31)) ^^^
        ((fd 25 MT z >>> 2) &&& 1082401) * ((M >>> (5 * 2)) &&& 31)) ^^^
        ((fd 25 MT z >>> 3) &&& 1082401) * ((M >>> (5 * 3)) &&& 31)) ^^^
        ((fd 25 MT z >>> 4) &&& 1082401) * ((M >>> (5 * 4)) &&& 31) := rfl
  have hterm : ∀ k < 5, fd 25 (((MT >>> k) &&& 1082401 * repU) * ((M >>> (5 * k)) &&& 31)) z =
      ((fd 25 MT z >>> k) &&& 1082401) * ((M >>> (5 * k)) &&& 31) := by
    intro k hk
    have h1 : (1082401 : ℕ) < 2 ^ 25 := by norm_num
    rw [Nat.mul_comm, lane_mul, Nat.mul_comm]
    · rw [fd25_and_rep h1, if_pos hz, fd25_shr_and]
      exact lt_of_lt_of_le (by norm_num : (1082401 : ℕ) < 2 ^ 21)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro y
      rw [fd25_and_rep h1]
      split_ifs
      · rw [fd25_shr_and, Nat.mul_comm]
        · exact spr_bound _ k _ (and31_lt _)
        · exact lt_of_lt_of_le (by norm_num : (1082401 : ℕ) < 2 ^ 21)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
      · rw [Nat.mul_zero]
        norm_num
  have h0 : fd 25 0 z = 0 := by
    rw [fd_eq, Nat.zero_shiftRight, Nat.zero_mod]
  unfold prodR
  rw [letN_eq, hT, hM, fd25_xor, fd25_xor, fd25_xor, fd25_xor, fd25_xor, h0,
    hterm 0 (by omega), hterm 1 (by omega), hterm 2 (by omega), hterm 3 (by omega),
    hterm 4 (by omega)]

theorem fold25_lane (a b z : ℕ) :
    (fold25 (a ^^^ b)).testBit (25 * z) = false ↔ fd 25 a z = fd 25 b z := by
  rw [Bool.eq_false_iff, Ne, testBit_fold25]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro d
    rw [fd25_testBit, fd25_testBit]
    by_cases hd : d < 25
    · have h1 : (a ^^^ b).testBit (25 * z + d) ≠ true := fun h' => h ⟨d, hd, h'⟩
      rw [Nat.testBit_xor] at h1
      simp only [hd, decide_true, Bool.true_and]
      revert h1
      cases a.testBit (25 * z + d) <;> cases b.testBit (25 * z + d) <;> simp
    · simp [hd]
  · rintro h ⟨d, hd, h'⟩
    have h1 := congrArg (fun x => x.testBit d) h
    simp only [fd25_testBit, hd, decide_true, Bool.true_and] at h1
    rw [Nat.testBit_xor, h1] at h'
    simp at h'

theorem mul25_lt (A B : ℕ) : mul25 A B < 2 ^ 25 := by
  have hT : mul25 A B = (((((0 ^^^ ((A >>> 0) &&& 1082401) * ((B >>> (5 * 0)) &&& 31)) ^^^
      ((A >>> 1) &&& 1082401) * ((B >>> (5 * 1)) &&& 31)) ^^^
      ((A >>> 2) &&& 1082401) * ((B >>> (5 * 2)) &&& 31)) ^^^
      ((A >>> 3) &&& 1082401) * ((B >>> (5 * 3)) &&& 31)) ^^^
      ((A >>> 4) &&& 1082401) * ((B >>> (5 * 4)) &&& 31)) := rfl
  rw [hT]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (by norm_num) ?_) ?_) ?_) ?_) ?_ <;>
  exact spr_bound _ _ _ (and31_lt _)

theorem fd5_testBit (X i d : ℕ) :
    (fd 5 X i).testBit d = (decide (d < 5) && X.testBit (5 * i + d)) := by
  rw [fd_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem par_spec : ∀ r < 32, ∀ v < 32, (2523490710 : ℕ).testBit (r &&& v) =
    (((((r.testBit 0 && v.testBit 0) ^^ (r.testBit 1 && v.testBit 1)) ^^
      (r.testBit 2 && v.testBit 2)) ^^ (r.testBit 3 && v.testBit 3)) ^^
      (r.testBit 4 && v.testBit 4)) := by
  decide +kernel

@[expose] noncomputable def mvRec (M v n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight 2523490710
      (Nat.land (fd 5 M i) v)) 1) i)) n

theorem testBit_mvRec (M v d n : ℕ) :
    (mvRec M v n).testBit d = (decide (d < n) && (2523490710 : ℕ).testBit (fd 5 M d &&& v)) := by
  induction n with
  | zero => simp [mvRec]
  | succ n ih =>
    have hs : mvRec M v (n + 1) = Nat.lor (mvRec M v n) (Nat.shiftLeft (Nat.land
        (Nat.shiftRight 2523490710 (Nat.land (fd 5 M n) v)) 1) n) := rfl
    rw [hs, lor_eq, Nat.testBit_or, ih, shl_eq, Nat.testBit_shiftLeft, land_eq, shr_eq,
      testBit_bit1, land_eq]
    by_cases h : d < n
    · have h1 : d < n + 1 := by omega
      have h2 : ¬ (d ≥ n) := by omega
      simp [h, h1, h2]
    · by_cases h' : d = n
      · subst h'
        simp
      · have h1 : ¬ d < n + 1 := by omega
        have h3 : d - n ≠ 0 := by omega
        simp [h, h1, h3]

theorem mv_entry (M v : ℕ) (hv : v < 32) (i : Fin 5) :
    (if (mv M v).testBit i then (1 : ZMod 2) else 0) = (matOf M *ᵥ vdec v) i := by
  have he : mv M v = mvRec M v 5 := rfl
  have hr : fd 5 M i < 32 := by
    rw [fd_eq]
    exact Nat.mod_lt _ (by norm_num)
  rw [he, testBit_mvRec]
  simp only [i.2, decide_true, Bool.true_and]
  rw [par_spec _ hr _ hv]
  simp only [fd5_testBit, Matrix.mulVec, dotProduct,
    Fin.sum_univ_five, matOf, vdec, Matrix.of_apply]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceLT, decide_true, Bool.true_and]
  exact ite_xor5 _ _ _ _ _ _ _ _ _ _

theorem mv_spec (M v : ℕ) (hv : v < 32) : mv M v = v ↔ matOf M *ᵥ vdec v = vdec v := by
  have hb : ∀ d, 5 ≤ d → (mv M v).testBit d = false := by
    intro d hd
    have he : mv M v = mvRec M v 5 := rfl
    rw [he, testBit_mvRec]
    simp
    omega
  constructor
  · intro h
    funext i
    rw [← mv_entry M v hv i, h]
    rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro d
    by_cases hd : d < 5
    · apply ite_inj2
      have := mv_entry M v hv ⟨d, hd⟩
      rw [this, h]
      rfl
    · rw [hb d (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
        (by rw [show (32 : ℕ) = 2 ^ 5 from rfl]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] noncomputable def vmRec (M v n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (fd 5 M i)) (bitB v i)) n

theorem testBit_vmRec (M v d n : ℕ) :
    (vmRec M v n).testBit d = xorL (fun i => v.testBit i && (fd 5 M i).testBit d) n := by
  induction n with
  | zero => simp [vmRec, xorL]
  | succ n ih =>
    have hs : vmRec M v (n + 1) =
        Bool.rec (motive := fun _ => ℕ) (vmRec M v n) (Nat.xor (vmRec M v n) (fd 5 M n))
          (bitB v n) := rfl
    rw [hs, xorL, ← ih, bitB_eq]
    cases v.testBit n
    · simp
    · rw [xor_eq, Nat.testBit_xor]
      simp

theorem vm_spec (M v : ℕ) (hv : v < 32) : vm M v = v ↔ (matOf M)ᵀ *ᵥ vdec v = vdec v := by
  have he : vm M v = vmRec M v 5 := rfl
  have hent : ∀ j : Fin 5, (if (vm M v).testBit j then (1 : ZMod 2) else 0) =
      ((matOf M)ᵀ *ᵥ vdec v) j := by
    intro j
    rw [he, testBit_vmRec]
    simp only [xorL, fd5_testBit, j.2, decide_true, Bool.true_and, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, matOf, vdec, Matrix.transpose_apply, Matrix.of_apply]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    exact ite_xor5' _ _ _ _ _ _ _ _ _ _
  have hb : ∀ d, 5 ≤ d → (vm M v).testBit d = false := by
    intro d hd
    rw [he, testBit_vmRec]
    have h5 : ¬ d < 5 := by omega
    simp [xorL, fd5_testBit, h5]
  constructor
  · intro h
    funext j
    rw [← hent j, h]
    rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro d
    by_cases hd : d < 5
    · apply ite_inj2
      have := hent ⟨d, hd⟩
      rw [this, h]
      rfl
    · rw [hb d (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
        (by rw [show (32 : ℕ) = 2 ^ 5 from rfl]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem beq_rec01 (b : Bool) : Nat.beq (Bool.rec (motive := fun _ => ℕ) 0 1 b) 1 = b := by
  cases b <;> rfl

theorem recOK_spec {MT r : ℕ} (h : recOK MT r = true) :
    fd 25 MT (rx r) = rM r ∧ rM r &&& 15961120 = 0 ∧ rM r &&& 17043521 = 17043521 ∧
      mul25 (rM r) (rM r) = 17043521 ∧ rM r ≠ 17043521 ∧
      (∀ z < 191, ((rcm r).testBit z = true ↔
          (fold25 (prodL (rM r) MT ^^^ prodR (rM r) MT)).testBit (25 * z) = false ∧ z ≠ rx r) ∧
        ((rcm r).testBit z = true →
          rowAt r z < 191 ∧ fd 25 MT (rowAt r z) = fd 25 (prodL (rM r) MT) z)) ∧
      (∀ v < 32, ((rfix r).testBit v = true ↔ mv (rM r) v = v) ∧
        ((rfixT r).testBit v = true ↔ vm (rM r) v = v)) := by
  unfold recOK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true, allN_spec, eqB_eq, impB_eq, notB_eq, bitB_eq,
    beq_rec01, Nat.beq_eq, Nat.blt_eq, land_eq, xor_eq, Nat.mul_eq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := h
  have key : ∀ (a : Bool) {x y : ℕ}, (a == Nat.beq x y) = true → (a = true ↔ x = y) := by
    intro a x y hab
    by_cases hxy : x = y
    · subst hxy
      rw [Nat.beq_refl] at hab
      cases a <;> simp_all
    · have hf : Nat.beq x y = false :=
        Bool.eq_false_iff.2 fun h => hxy (Nat.eq_of_beq_eq_true h)
      rw [hf] at hab
      cases a <;> simp_all
  refine ⟨h1, h2, h3, h4, fun he => ?_, fun z hz => ?_, fun v hv => ?_⟩
  · rw [he, Nat.beq_refl] at h5
    exact absurd h5 (by decide)
  · obtain ⟨ha, hb⟩ := h6 z hz
    have hc : ((rcm r).testBit z = true ↔
        (fold25 (prodL (rM r) MT ^^^ prodR (rM r) MT)).testBit (25 * z) = false ∧ z ≠ rx r) := by
      revert ha
      cases (rcm r).testBit z <;> cases (fold25 (prodL (rM r) MT ^^^ prodR (rM r) MT)).testBit
        (25 * z) <;> by_cases hzx : z = rx r <;> simp [hzx]
    refine ⟨hc, fun hz' => ?_⟩
    have hd := hc.1 hz'
    have hzb : Nat.beq z (rx r) = false := by
      cases hzr : Nat.beq z (rx r)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hzr) hd.2
    have hd' : (!(fold25 (prodL (rM r) MT ^^^ prodR (rM r) MT)).testBit (25 * z) &&
        !Nat.beq z (rx r)) = true := by
      simp [hd.1, hzb]
    rw [hd'] at hb
    simpa using hb
  · obtain ⟨ha, hb⟩ := h7 v hv
    exact ⟨key _ ha, key _ hb⟩

theorem recsFrom_spec (MT : ℕ) : ∀ (RL : List ℕ) (i : ℕ), recsFrom MT RL i = true →
    RL.length + i = 191 ∧ ∀ m < RL.length, rx (RL.getD m 0) = i + m ∧ recOK MT (RL.getD m 0) = true
  | [], i, h => by
    have h' : Nat.beq i 191 = true := h
    simp only [Nat.beq_eq] at h'
    simp [h']
  | r :: RL, i, h => by
    have h' : andB (Nat.beq (rx r) i) (andB (recOK MT r) (recsFrom MT RL (i + 1))) = true := h
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := recsFrom_spec MT RL (i + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
    cases m with
    | zero => simpa [h1] using h2
    | succ m =>
      have hm' : m < RL.length := by simp only [List.length_cons] at hm; omega
      obtain ⟨e1, e2⟩ := ih2 m hm'
      refine ⟨?_, ?_⟩
      · simp only [List.getD_cons_succ]
        rw [e1]
        omega
      · simpa using e2

theorem diag_bits : ∀ i < 5, ∀ j < 5, j < i → (15961120 : ℕ).testBit (5 * i + j) = true := by
  decide +kernel

theorem recsOK_sound {MT : ℕ} {RL : List ℕ} (h : recsOK MT RL = true) :
    RL.length = 191 ∧ ∀ i < 191,
      rx (recAt RL i) = i ∧ rM (recAt RL i) = lane MT i ∧
      IsUni (matOf (lane MT i)) ∧ matOf (lane MT i) * matOf (lane MT i) = 1 ∧
      matOf (lane MT i) ≠ 1 ∧
      (∀ v < 32, ((rfix (recAt RL i)).testBit v ↔
          matOf (lane MT i) *ᵥ vdec v = vdec v) ∧
        ((rfixT (recAt RL i)).testBit v ↔ (matOf (lane MT i))ᵀ *ᵥ vdec v = vdec v)) ∧
      ∀ j < 191, (matOf (lane MT i) = matOf (lane MT j) → i = j) ∧
        ((rcm (recAt RL i)).testBit j ↔
          i ≠ j ∧ matOf (lane MT i) * matOf (lane MT j) = matOf (lane MT j) * matOf (lane MT i)) ∧
        ((rcm (recAt RL i)).testBit j →
          rowAt (recAt RL i) j < 191 ∧
            matOf (lane MT (rowAt (recAt RL i) j)) = matOf (lane MT i) * matOf (lane MT j)) := by
  obtain ⟨hlen, hall⟩ := recsFrom_spec MT RL 0 h
  rw [Nat.add_zero] at hlen
  have hrec : ∀ i < 191, rx (recAt RL i) = i ∧ recOK MT (recAt RL i) = true := by
    intro i hi
    obtain ⟨e1, e2⟩ := hall i (by omega)
    exact ⟨by rw [recAt, e1, Nat.zero_add], e2⟩
  have hlane : ∀ i < 191, rM (recAt RL i) = lane MT i := by
    intro i hi
    obtain ⟨e1, e2⟩ := hrec i hi
    have := (recOK_spec e2).1
    rw [e1] at this
    exact this.symm
  have hlt : ∀ i, lane MT i < 2 ^ 25 := fun i => fd25_lt MT i
  have hne1 : ∀ i < 191, lane MT i ≠ 17043521 := by
    intro i hi
    rw [← hlane i hi]
    exact (recOK_spec (hrec i hi).2).2.2.2.2.1
  refine ⟨hlen, fun i hi => ?_⟩
  obtain ⟨hx, hok⟩ := hrec i hi
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := recOK_spec hok
  rw [hlane i hi] at h2 h3 h4 h5 h6 h7
  have hcomm : ∀ j < 191, ((rcm (recAt RL i)).testBit j = true ↔
      i ≠ j ∧ mul25 (lane MT i) (lane MT j) = mul25 (lane MT j) (lane MT i)) := by
    intro j hj
    rw [(h6 j hj).1, fold25_lane, fd25_prodL _ _ hj, fd25_prodR _ _ hj, hx]
    have e : (fd 25 MT j) = lane MT j := rfl
    rw [e]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h' => h2 h'.symm, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h' => h1 h'.symm⟩
  have hprod : ∀ j < 191, (rcm (recAt RL i)).testBit j = true →
      rowAt (recAt RL i) j < 191 ∧
        lane MT (rowAt (recAt RL i) j) = mul25 (lane MT i) (lane MT j) := by
    intro j hj hb
    obtain ⟨e1, e2⟩ := (h6 j hj).2 hb
    exact ⟨e1, by rw [lane, e2, fd25_prodL _ _ hj]; rfl⟩
  refine ⟨hx, hlane i hi, ⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_, fun v hv => ?_,
    fun j hj => ⟨fun heq => ?_, ?_, fun hb => ?_⟩⟩
  · have hb := diag_bits a a.2 b b.2 hab
    have h0 := congrArg (fun n => n.testBit (5 * (a : ℕ) + b)) h2
    simp only [Nat.testBit_and, hb, Bool.and_true, Nat.zero_testBit] at h0
    simp only [matOf, Matrix.of_apply, h0]
    rfl
  · have hb : (17043521 : ℕ).testBit (5 * (a : ℕ) + a) = true := by
      rw [testBit_I a a.2 a a.2]
      simp
    have h0 := congrArg (fun n => n.testBit (5 * (a : ℕ) + a)) h3
    simp only [Nat.testBit_and, hb, Bool.and_true] at h0
    simp only [matOf, Matrix.of_apply, h0]
    rfl
  · rw [← mul25_spec', h4, matOf_one]
  · intro h1
    exact h5 (matOf_inj (hlt i) (by norm_num) (h1.trans matOf_one.symm))
  · obtain ⟨ha, hb⟩ := h7 v hv
    rw [mv_spec _ _ hv] at ha
    rw [vm_spec _ _ hv] at hb
    exact ⟨ha, hb⟩
  · by_contra hij
    have he : lane MT i = lane MT j := matOf_inj (hlt i) (hlt j) heq
    have hb : (rcm (recAt RL i)).testBit j = true := (hcomm j hj).2 ⟨hij, by rw [he]⟩
    obtain ⟨he1, he2⟩ := hprod j hj hb
    rw [← he, h4] at he2
    exact hne1 _ he1 he2
  · rw [hcomm j hj, ← mul25_spec', ← mul25_spec']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, matOf_inj (mul25_lt _ _) (mul25_lt _ _) h2⟩
  · obtain ⟨e1, e2⟩ := hprod j hj hb
    exact ⟨e1, by rw [e2, mul25_spec']⟩

theorem singMask_spec {p : ℕ} (hp : p < 2 ^ 15) (h : singMask.testBit p) :
    ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧ symC p *ᵥ v = 0 := by
  have hp' : p < 32768 := lt_of_lt_of_le hp (by norm_num)
  obtain ⟨w, hw, hz⟩ := (testBit_srec p 31).1 h
  rw [zMask_eq, testBit_zrec _ hp'] at hz
  refine ⟨vdec (w + 1), ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (x := w + 1) (by omega)
    have hi5 : i < 5 := by
      by_contra hc
      have hlt : w + 1 < 2 ^ i :=
        lt_of_lt_of_le (by omega : w + 1 < 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hlt] at hi
      exact absurd hi (by simp)
    have h1 := congrFun h0 ⟨i, hi5⟩
    simp only [vdec, hi, if_true, Pi.zero_apply] at h1
    exact absurd h1 (by decide)
  · funext i
    rw [row_eq hp, hz i i.2]
    rfl

theorem exists_symC (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hP : Pᵀ = P) :
    ∃ p < 2 ^ 15, symC p = P := by
  let P' : ℕ → ℕ → ZMod 2 := fun a b => if h : a < 5 ∧ b < 5 then P ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  let f : ℕ → Bool := fun k => decide (P' (fd 5 symPos k / 5) (fd 5 symPos k % 5) = 1)
  refine ⟨ofBitsF f 15, ofBitsF_lt f 15, ?_⟩
  have hs : ∀ i j : Fin 5, fd 4 symIdx (5 * (i : ℕ) + j) < 15 ∧
      fd 5 symPos (fd 4 symIdx (5 * (i : ℕ) + j)) = 5 * min (i : ℕ) j + max (i : ℕ) j := by
    decide +kernel
  have hz : ∀ x : ZMod 2, (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by decide
  ext i j
  obtain ⟨h1, h2⟩ := hs i j
  have hsym : P' (min (i : ℕ) j) (max (i : ℕ) j) = P i j := by
    have hi := i.2
    have hj := j.2
    rcases le_total (i : ℕ) j with h | h
    · simp only [P', min_eq_left h, max_eq_right h, hi, hj, and_self, dite_true]
    · simp only [P', min_eq_right h, max_eq_left h, hi, hj, and_self, dite_true]
      rw [← congrFun (congrFun hP i) j]
      rfl
  simp only [symC, Matrix.of_apply, testBit_ofBitsF, h1, decide_true, Bool.true_and, f, h2]
  have hd : (5 * min (i : ℕ) j + max (i : ℕ) j) / 5 = min (i : ℕ) j := by omega
  have hm : (5 * min (i : ℕ) j + max (i : ℕ) j) % 5 = max (i : ℕ) j := by omega
  rw [hd, hm, hsym, hz]

theorem newOnly_eq (r : ℕ) (Yl : List ℕ) : newOnly r Yl = Yl.map (rowAt r) ++ [rx r] := by
  induction Yl with
  | nil => rfl
  | cons y Yl ih =>
    change rowAt r y :: newOnly r Yl = _
    rw [ih, List.map_cons, List.cons_append]

theorem appendL_eq (a b : List ℕ) : appendL a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    change x :: appendL a b = _
    rw [ih, List.cons_append]

theorem testBit_newMask (r : ℕ) (Yl : List ℕ) (Ym z : ℕ) :
    (newMask r Yl Ym).testBit z = true ↔
      Ym.testBit z = true ∨ z = rx r ∨ ∃ y ∈ Yl, z = rowAt r y := by
  induction Yl with
  | nil =>
    change (Nat.lor Ym (Nat.shiftLeft 1 (rx r))).testBit z = true ↔ _
    rw [lor_eq, shl_eq, Nat.testBit_or, Bool.or_eq_true, Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, decide_eq_true_iff]
    have e : rx r = z ↔ z = rx r := eq_comm
    rw [e]
    simp
  | cons y Yl ih =>
    change (Nat.lor (newMask r Yl Ym) (Nat.shiftLeft 1 (rowAt r y))).testBit z = true ↔ _
    rw [lor_eq, shl_eq, Nat.testBit_or, Bool.or_eq_true, ih, Nat.shiftLeft_eq, one_mul,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro ((h | h | ⟨y', hy', rfl⟩) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨y', List.mem_cons.2 (Or.inr hy'), rfl⟩)
      · exact Or.inr (Or.inr ⟨y, List.mem_cons.2 (Or.inl rfl), h.symm⟩)
    · rintro (h | h | ⟨y', hy', rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases List.mem_cons.1 hy' with rfl | hy'
        · exact Or.inr rfl
        · exact Or.inl (Or.inr (Or.inr ⟨y', hy', rfl⟩))

theorem filterP_eq (r Ym' : ℕ) (nw l : List ℕ) :
    filterP r Ym' nw l = l.filter (fun z =>
      andB (andB (bitB (rcm r) (rx z)) (notB (bitB Ym' (rx z)))) (canonZ z nw)) := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filterP r Ym' nw l) (z :: filterP r Ym' nw l)
      (andB (andB (bitB (rcm r) (rx z)) (notB (bitB Ym' (rx z)))) (canonZ z nw)) = _
    by_cases hc : andB (andB (bitB (rcm r) (rx z)) (notB (bitB Ym' (rx z)))) (canonZ z nw) = true
    · rw [hc]
      change z :: filterP r Ym' nw l = _
      rw [ih]
      simp [List.filter_cons, hc]
    · rw [Bool.not_eq_true] at hc
      rw [hc]
      change filterP r Ym' nw l = _
      rw [ih]
      simp [List.filter_cons, hc]

theorem canonZ_spec (z : ℕ) (nw : List ℕ) :
    canonZ z nw = true ↔ ∀ w ∈ nw, rx z < rowAt z w := by
  induction nw with
  | nil =>
    change true = true ↔ _
    simp
  | cons w nw ih =>
    change andB (Nat.blt (rx z) (rowAt z w)) (canonZ z nw) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, Nat.blt_eq, List.forall_mem_cons]

theorem walkList_spec (g : ℕ → List ℕ → Bool) : ∀ (pre : List ℕ) (r : ℕ) (rest : List ℕ),
    List.rec (motive := fun _ => Bool) true (fun r rest acc => andB (g r rest) acc)
      (pre ++ r :: rest) = true → g r rest = true
  | [], r, rest, h => by
    change andB (g r rest) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    exact h.1
  | p :: pre, r, rest, h => by
    change andB (g p (pre ++ r :: rest)) _ = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    exact walkList_spec g pre r rest h.2

theorem mem_rest {L pre rest : List ℕ} {r z : ℕ} (hs : L.Pairwise (· < ·))
    (hL : L = pre ++ r :: rest) (hz : z ∈ L) (hrz : r < z) : z ∈ rest := by
  subst hL
  rw [List.pairwise_append] at hs
  rcases List.mem_append.1 hz with h | h
  · have := hs.2.2 z h r (by simp)
    omega
  · rcases List.mem_cons.1 h with h | h
    · omega
    · exact h

def inH (MT : ℕ) (Yl : List ℕ) (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  x = 1 ∨ ∃ d ∈ Yl, matOf (lane MT d) = x

theorem map_range_getD (l : List ℕ) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem walk_sound {MT S : ℕ} {RL : List ℕ} (hR : recsOK MT RL = true)
    (hW : walkP S 7 0 0 [] 4294967295 4294967295 [] RL = true) (X : Finset ℕ)
    (hX : ∀ a ∈ X, a < 191)
    (hcl : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → (rcm (recAt RL a)).testBit b ∧ rowAt (recAt RL a) b ∈ X) :
    ∃ B : List ℕ, (∀ b ∈ B, b ∈ X) ∧ X.card + 1 = 2 ^ B.length ∧ B.length ≤ 6 ∧
      nodeOK S B.length (andMask rfix RL X) (andMask rfixT RL X) (B.map (recAt RL)) = true := by
  obtain ⟨hlen, hrec⟩ := recsOK_sound hR
  have hrx : ∀ a ∈ X, rx (recAt RL a) = a := fun a ha => (hrec a (hX a ha)).1
  have hinj : ∀ a ∈ X, ∀ c ∈ X, matOf (lane MT a) = matOf (lane MT c) → a = c :=
    fun a ha c hc h => ((hrec a (hX a ha)).2.2.2.2.2.2 c (hX c hc)).1 h
  have hsq : ∀ a ∈ X, matOf (lane MT a) * matOf (lane MT a) = 1 :=
    fun a ha => (hrec a (hX a ha)).2.2.2.1
  have hne : ∀ a ∈ X, matOf (lane MT a) ≠ 1 := fun a ha => (hrec a (hX a ha)).2.2.2.2.1
  have hfix : ∀ a ∈ X, ∀ v < 32,
      ((rfix (recAt RL a)).testBit v ↔ matOf (lane MT a) *ᵥ vdec v = vdec v) ∧
        ((rfixT (recAt RL a)).testBit v ↔ (matOf (lane MT a))ᵀ *ᵥ vdec v = vdec v) :=
    fun a ha => (hrec a (hX a ha)).2.2.2.2.2.1
  have hprod : ∀ a ∈ X, ∀ c ∈ X, a ≠ c → rowAt (recAt RL a) c ∈ X ∧
      matOf (lane MT (rowAt (recAt RL a) c)) = matOf (lane MT a) * matOf (lane MT c) ∧
      matOf (lane MT a) * matOf (lane MT c) = matOf (lane MT c) * matOf (lane MT a) := by
    intro a ha c hc hac
    obtain ⟨h1, h2⟩ := hcl a ha c hc hac
    obtain ⟨-, h3, h4⟩ := (hrec a (hX a ha)).2.2.2.2.2.2 c (hX c hc)
    exact ⟨h2, (h4 h1).2, ((h3.1 h1).2)⟩
  have hcomm : ∀ a ∈ X, ∀ c ∈ X,
      matOf (lane MT a) * matOf (lane MT c) = matOf (lane MT c) * matOf (lane MT a) := by
    intro a ha c hc
    by_cases hac : a = c
    · rw [hac]
    · exact (hprod a ha c hc hac).2.2
  have main : ∀ n (Bi Yl : List ℕ) (Ym f fT : ℕ) (L : List ℕ),
      (∀ a ∈ Yl, a ∈ X) → Yl.Nodup →
      (∀ x y, inH MT Yl x → inH MT Yl y → inH MT Yl (x * y)) →
      (∀ z, Ym.testBit z = true ↔ z ∈ Yl) →
      Yl.length + 1 = 2 ^ Bi.length → (∀ b ∈ Bi, b ∈ Yl) →
      f < 2 ^ 32 →
      (∀ v < 32, f.testBit v = true ↔ ∀ b ∈ Bi, (rfix (recAt RL b)).testBit v = true) →
      fT < 2 ^ 32 →
      (∀ v < 32, fT.testBit v = true ↔ ∀ b ∈ Bi, (rfixT (recAt RL b)).testBit v = true) →
      (∀ v < 32, (∀ b ∈ Bi, (rfix (recAt RL b)).testBit v = true) →
        ∀ a ∈ Yl, (rfix (recAt RL a)).testBit v = true) →
      (∀ v < 32, (∀ b ∈ Bi, (rfixT (recAt RL b)).testBit v = true) →
        ∀ a ∈ Yl, (rfixT (recAt RL a)).testBit v = true) →
      L.Pairwise (· < ·) →
      (∀ z ∈ X, z ∉ Yl → (∀ y ∈ Yl, z < rowAt (recAt RL z) y) → z ∈ L) →
      Bi.length + n = 7 →
      walkP S n Bi.length Ym Yl f fT (Bi.map (recAt RL)) (L.map (recAt RL)) = true →
      ∃ B : List ℕ, (∀ b ∈ B, b ∈ X) ∧ X.card + 1 = 2 ^ B.length ∧ B.length ≤ 6 ∧
        nodeOK S B.length (andMask rfix RL X) (andMask rfixT RL X) (B.map (recAt RL)) = true := by
    intro n
    induction n with
    | zero =>
      intro Bi Yl Ym f fT L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw
      exact absurd hw (by change ¬ false = true; decide)
    | succ n ih =>
      intro Bi Yl Ym f fT L hY1 hY2 hY3 hY4 hY5 hB1 hf1 hf2 hT1 hT2 hF hFT hLs hL2 hlen7 hw
      change andB (nodeOK S Bi.length f fT (Bi.map (recAt RL)))
        (List.rec (motive := fun _ => Bool) true (fun r rest acc => andB
          (letB (newMask r Yl Ym) fun Ym' =>
            letB (Nat.land f (rfix r)) fun f' => letB (Nat.land fT (rfixT r)) fun fT' =>
              walkP S n (Nat.succ Bi.length) Ym' (appendL (newOnly r Yl) Yl) f' fT'
                (List.cons r (Bi.map (recAt RL))) (filterP r Ym' (newOnly r Yl) rest)) acc)
          (L.map (recAt RL))) = true at hw
      rw [andB_eq, Bool.and_eq_true] at hw
      obtain ⟨hnode, hlist⟩ := hw
      by_cases hall : ∀ a ∈ X, a ∈ Yl
      · refine ⟨Bi, fun b hb => hY1 b (hB1 b hb), ?_, by omega, ?_⟩
        · have hXY : X = Yl.toFinset := by
            ext a
            rw [List.mem_toFinset]
            exact ⟨hall a, hY1 a⟩
          rw [hXY, List.toFinset_card_of_nodup hY2, hY5]
        · have hmask : ∀ (sel : ℕ → ℕ) (g : ℕ), g < 2 ^ 32 →
              (∀ v < 32, g.testBit v = true ↔ ∀ b ∈ Bi, (sel (recAt RL b)).testBit v = true) →
              (∀ v < 32, (∀ b ∈ Bi, (sel (recAt RL b)).testBit v = true) →
                ∀ a ∈ Yl, (sel (recAt RL a)).testBit v = true) →
              andMask sel RL X = g := by
            intro sel g hg hg2 hg3
            apply Nat.eq_of_testBit_eq
            intro v
            by_cases hv : v < 32
            · rw [Bool.eq_iff_iff, testBit_andMask sel RL X hv, hg2 v hv]
              constructor
              · intro h b hb
                exact h b (hY1 b (hB1 b hb)) (hX b (hY1 b (hB1 b hb)))
              · intro h a ha _
                exact hg3 v hv h a (hall a ha)
            · have h32 : 2 ^ 32 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
              rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (andMask_lt sel RL X) h32),
                Nat.testBit_lt_two_pow (lt_of_lt_of_le hg h32)]
          rw [hmask rfix f hf1 hf2 hF, hmask rfixT fT hT1 hT2 hFT]
          exact hnode
      · push Not at hall
        have hne' : (X.filter (fun a => a ∉ Yl)).Nonempty := by
          obtain ⟨a, ha, haY⟩ := hall
          exact ⟨a, Finset.mem_filter.2 ⟨ha, haY⟩⟩
        obtain ⟨hbX, hbY⟩ := Finset.mem_filter.1 (Finset.min'_mem _ hne')
        have hbmin : ∀ a ∈ X, a ∉ Yl → (X.filter (fun a => a ∉ Yl)).min' hne' ≤ a :=
          fun a ha haY => Finset.min'_le _ _ (Finset.mem_filter.2 ⟨ha, haY⟩)
        generalize (X.filter (fun a => a ∉ Yl)).min' hne' = b at hbX hbY hbmin
        have hYX : ∀ y ∈ Yl, y ≠ b := fun y hy hyb => hbY (hyb ▸ hy)
        have hpb : ∀ y ∈ Yl, rowAt (recAt RL b) y ∈ X ∧
            matOf (lane MT (rowAt (recAt RL b) y)) = matOf (lane MT b) * matOf (lane MT y) :=
          fun y hy => ⟨(hprod b hbX y (hY1 y hy) (hYX y hy).symm).1,
            (hprod b hbX y (hY1 y hy) (hYX y hy).symm).2.1⟩
        have hBB : ∀ x, matOf (lane MT b) * (matOf (lane MT b) * x) = x := by
          intro x
          rw [← Matrix.mul_assoc, hsq b hbX, Matrix.one_mul]
        have hHc : ∀ x, inH MT Yl x → x * matOf (lane MT b) = matOf (lane MT b) * x := by
          rintro x (rfl | ⟨d, hd, rfl⟩)
          · rw [Matrix.one_mul, Matrix.mul_one]
          · exact hcomm d (hY1 d hd) b hbX
        have n3 : ∀ y ∈ Yl, rowAt (recAt RL b) y ≠ b := by
          intro y hy he
          have h := (hpb y hy).2
          rw [he] at h
          apply hne y (hY1 y hy)
          rw [← hBB (matOf (lane MT y)), ← h, hsq b hbX]
        have n4 : ∀ y1 ∈ Yl, ∀ y2 ∈ Yl, rowAt (recAt RL b) y1 = rowAt (recAt RL b) y2 →
            y1 = y2 := by
          intro y1 hy1 y2 hy2 he
          apply hinj y1 (hY1 y1 hy1) y2 (hY1 y2 hy2)
          rw [← hBB (matOf (lane MT y1)), ← hBB (matOf (lane MT y2)), ← (hpb y1 hy1).2,
            ← (hpb y2 hy2).2, he]
        have n2 : ∀ y ∈ Yl, rowAt (recAt RL b) y ∉ Yl := by
          intro y hy hm
          have h := (hpb y hy).2
          have hb' : matOf (lane MT (rowAt (recAt RL b) y)) * matOf (lane MT y) =
              matOf (lane MT b) := by
            rw [h, Matrix.mul_assoc, hsq y (hY1 y hy), Matrix.mul_one]
          rcases hY3 _ _ (Or.inr ⟨_, hm, rfl⟩) (Or.inr ⟨y, hy, rfl⟩) with h1 | ⟨d, hd, h1⟩
          · rw [hb'] at h1
            exact hne b hbX h1
          · rw [hb'] at h1
            exact hbY (hinj d (hY1 d hd) b hbX h1 ▸ hd)
        have hrb : rx (recAt RL b) = b := hrx b hbX
        have hmemY : ∀ d, d ∈ appendL (newOnly (recAt RL b) Yl) Yl ↔
            (∃ y ∈ Yl, rowAt (recAt RL b) y = d) ∨ d = b ∨ d ∈ Yl := by
          intro d
          rw [appendL_eq, newOnly_eq, hrb]
          simp only [List.mem_append, List.mem_map, List.mem_singleton]
          constructor
          · rintro ((⟨y, hy, rfl⟩ | h) | h)
            · exact Or.inl ⟨y, hy, rfl⟩
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · rintro (⟨y, hy, rfl⟩ | h | h)
            · exact Or.inl (Or.inl ⟨y, hy, rfl⟩)
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
        have hH' : ∀ x, inH MT (appendL (newOnly (recAt RL b) Yl) Yl) x ↔
            inH MT Yl x ∨ inH MT Yl (matOf (lane MT b) * x) := by
          intro x
          constructor
          · rintro (rfl | ⟨d, hd, rfl⟩)
            · exact Or.inl (Or.inl rfl)
            · rcases (hmemY d).1 hd with ⟨y, hy, rfl⟩ | rfl | hd'
              · right
                right
                refine ⟨y, hy, ?_⟩
                rw [(hpb y hy).2, hBB]
              · right
                left
                exact hsq d hbX
              · exact Or.inl (Or.inr ⟨d, hd', rfl⟩)
          · rintro ((rfl | ⟨d, hd, rfl⟩) | (h1 | ⟨d, hd, h1⟩))
            · exact Or.inl rfl
            · exact Or.inr ⟨d, (hmemY d).2 (Or.inr (Or.inr hd)), rfl⟩
            · right
              refine ⟨b, (hmemY b).2 (Or.inr (Or.inl rfl)), ?_⟩
              rw [← hBB x, h1, Matrix.mul_one]
            · right
              refine ⟨_, (hmemY _).2 (Or.inl ⟨d, hd, rfl⟩), ?_⟩
              rw [(hpb d hd).2, h1, hBB]
        have hcomm' : ∀ x, inH MT Yl (matOf (lane MT b) * x) →
            x * matOf (lane MT b) = matOf (lane MT b) * x := by
          intro x hx
          have h := hHc _ hx
          have h2 : matOf (lane MT b) * x * matOf (lane MT b) = x := by rw [h, hBB]
          calc x * matOf (lane MT b)
              = matOf (lane MT b) * (matOf (lane MT b) * (x * matOf (lane MT b))) := (hBB _).symm
            _ = matOf (lane MT b) * (matOf (lane MT b) * x * matOf (lane MT b)) := by
                rw [Matrix.mul_assoc (matOf (lane MT b)) x]
            _ = matOf (lane MT b) * x := by rw [h2]
        have hY3' : ∀ x y, inH MT (appendL (newOnly (recAt RL b) Yl) Yl) x →
            inH MT (appendL (newOnly (recAt RL b) Yl) Yl) y →
            inH MT (appendL (newOnly (recAt RL b) Yl) Yl) (x * y) := by
          intro x y hx hy
          rw [hH'] at hx hy ⊢
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · exact Or.inl (hY3 _ _ hx hy)
          · right
            have e : matOf (lane MT b) * (x * y) = x * (matOf (lane MT b) * y) := by
              rw [← Matrix.mul_assoc, ← hHc x hx, Matrix.mul_assoc]
            rw [e]
            exact hY3 _ _ hx hy
          · right
            rw [← Matrix.mul_assoc]
            exact hY3 _ _ hx hy
          · left
            have e : x * y = (matOf (lane MT b) * x) * (matOf (lane MT b) * y) := by
              rw [← hcomm' x hx, Matrix.mul_assoc, ← Matrix.mul_assoc (matOf (lane MT b)),
                hsq b hbX, Matrix.one_mul]
            rw [e]
            exact hY3 _ _ hx hy
        have hY2' : (appendL (newOnly (recAt RL b) Yl) Yl).Nodup := by
          rw [appendL_eq, newOnly_eq, hrb]
          refine List.Nodup.append (List.Nodup.append (List.Nodup.map_on n4 hY2)
            (List.nodup_singleton b) ?_) hY2 ?_
          · intro a h1 h2
            rw [List.mem_singleton] at h2
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h1
            exact n3 y hy h2
          · intro a h1 h2
            rcases List.mem_append.1 h1 with h1 | h1
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h1
              exact n2 y hy h2
            · rw [List.mem_singleton] at h1
              subst h1
              exact hbY h2
        have hY1' : ∀ a ∈ appendL (newOnly (recAt RL b) Yl) Yl, a ∈ X := by
          intro a ha
          rcases (hmemY a).1 ha with ⟨y, hy, rfl⟩ | rfl | ha'
          · exact (hpb y hy).1
          · exact hbX
          · exact hY1 a ha'
        have hY4' : ∀ z, (newMask (recAt RL b) Yl Ym).testBit z = true ↔
            z ∈ appendL (newOnly (recAt RL b) Yl) Yl := by
          intro z
          rw [testBit_newMask, hY4, hmemY, hrb]
          constructor
          · rintro (h | h | ⟨y, hy, rfl⟩)
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl ⟨y, hy, rfl⟩
          · rintro (⟨y, hy, rfl⟩ | h | h)
            · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
        have hY5' : (appendL (newOnly (recAt RL b) Yl) Yl).length + 1 = 2 ^ (b :: Bi).length := by
          rw [appendL_eq, newOnly_eq]
          simp only [List.length_append, List.length_map, List.length_singleton,
            List.length_cons, List.length_nil, pow_succ]
          omega
        have hB1' : ∀ c ∈ b :: Bi, c ∈ appendL (newOnly (recAt RL b) Yl) Yl := by
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact (hmemY c).2 (Or.inr (Or.inl rfl))
          · exact (hmemY c).2 (Or.inr (Or.inr (hB1 c hc)))
        have hand : ∀ (g s : ℕ) (sel : ℕ → ℕ), (∀ v < 32, g.testBit v = true ↔
            ∀ c ∈ Bi, (sel (recAt RL c)).testBit v = true) → s = sel (recAt RL b) →
            ∀ v < 32, (Nat.land g s).testBit v = true ↔
              ∀ c ∈ b :: Bi, (sel (recAt RL c)).testBit v = true := by
          intro g s sel hg hs v hv
          rw [land_eq, Nat.testBit_and, Bool.and_eq_true, hg v hv, List.forall_mem_cons, hs]
          exact and_comm
        have hFix' : ∀ v < 32, (∀ c ∈ b :: Bi, (rfix (recAt RL c)).testBit v = true) →
            ∀ a ∈ appendL (newOnly (recAt RL b) Yl) Yl, (rfix (recAt RL a)).testBit v = true := by
          intro v hv h a ha
          rw [List.forall_mem_cons] at h
          rcases (hmemY a).1 ha with ⟨y, hy, rfl⟩ | rfl | ha'
          · have hyv := ((hfix y (hY1 y hy) v hv).1).1 (hF v hv h.2 y hy)
            have hbv := ((hfix b hbX v hv).1).1 h.1
            rw [(hfix _ (hpb y hy).1 v hv).1, (hpb y hy).2, ← Matrix.mulVec_mulVec, hyv, hbv]
          · exact h.1
          · exact hF v hv h.2 a ha'
        have hFixT' : ∀ v < 32, (∀ c ∈ b :: Bi, (rfixT (recAt RL c)).testBit v = true) →
            ∀ a ∈ appendL (newOnly (recAt RL b) Yl) Yl, (rfixT (recAt RL a)).testBit v = true := by
          intro v hv h a ha
          rw [List.forall_mem_cons] at h
          rcases (hmemY a).1 ha with ⟨y, hy, rfl⟩ | rfl | ha'
          · have hyv := ((hfix y (hY1 y hy) v hv).2).1 (hFT v hv h.2 y hy)
            have hbv := ((hfix b hbX v hv).2).1 h.1
            rw [(hfix _ (hpb y hy).1 v hv).2, (hpb y hy).2, Matrix.transpose_mul,
              ← Matrix.mulVec_mulVec, hbv, hyv]
          · exact h.1
          · exact hFT v hv h.2 a ha'
        have hbL : b ∈ L := by
          apply hL2 b hbX hbY
          intro y hy
          have h1 := (hpb y hy).1
          have h2 := hbmin _ h1 (n2 y hy)
          have h3 := n3 y hy
          omega
        obtain ⟨pre, rest, hsplit⟩ := List.append_of_mem hbL
        have hchild := walkList_spec _ (pre.map (recAt RL)) (recAt RL b) (rest.map (recAt RL))
          (by rw [← List.map_cons, ← List.map_append, ← hsplit]; exact hlist)
        simp only [letB_eq] at hchild
        rw [filterP_eq, List.filter_map] at hchild
        have hlen' : (b :: Bi).length + n = 7 := by
          simp only [List.length_cons]
          omega
        have hrestS : rest.Pairwise (· < ·) := by
          rw [hsplit, List.pairwise_append, List.pairwise_cons] at hLs
          exact hLs.2.1.2
        refine ih (b :: Bi) _ _ _ _ (rest.filter (fun z => andB (andB
          (bitB (rcm (recAt RL b)) (rx (recAt RL z)))
          (notB (bitB (newMask (recAt RL b) Yl Ym) (rx (recAt RL z)))))
          (canonZ (recAt RL z) (newOnly (recAt RL b) Yl)))) hY1' hY2' hY3' hY4' hY5' hB1'
          (lt_of_le_of_lt Nat.and_le_left hf1) (hand f _ rfix hf2 rfl)
          (lt_of_le_of_lt Nat.and_le_left hT1) (hand fT _ rfixT hT2 rfl) hFix' hFixT'
          (List.Pairwise.filter _ hrestS) ?_ hlen' hchild
        intro z hz hzY hzc
        rw [List.mem_filter]
        have hzY0 : z ∉ Yl := fun h => hzY ((hmemY z).2 (Or.inr (Or.inr h)))
        have hzb : z ≠ b := fun h => hzY ((hmemY z).2 (Or.inr (Or.inl h)))
        have hzL : z ∈ L := hL2 z hz hzY0 fun y hy => hzc y ((hmemY y).2 (Or.inr (Or.inr hy)))
        have hbz : b < z := lt_of_le_of_ne (hbmin z hz hzY0) (Ne.symm hzb)
        refine ⟨mem_rest hLs hsplit hzL hbz, ?_⟩
        have hrz : rx (recAt RL z) = z := hrx z hz
        have hc1 : bitB (rcm (recAt RL b)) (rx (recAt RL z)) = true := by
          rw [bitB_eq, hrz]
          exact (hcl b hbX z hz (Ne.symm hzb)).1
        have hc2 : bitB (newMask (recAt RL b) Yl Ym) (rx (recAt RL z)) = false := by
          rw [bitB_eq, hrz, Bool.eq_false_iff]
          intro h
          exact hzY ((hY4' z).1 h)
        have hc3 : canonZ (recAt RL z) (newOnly (recAt RL b) Yl) = true := by
          rw [canonZ_spec, hrz]
          intro w hw
          apply hzc w
          rw [appendL_eq]
          exact List.mem_append_left _ hw
        simp only [Function.comp_apply, hc1, hc2, hc3, andB_eq, notB_eq, Bool.not_false,
          Bool.and_self]
  have h0 := main 7 [] [] 0 4294967295 4294967295 (List.range 191)
    (by simp) List.nodup_nil
    (by
      rintro x y (rfl | ⟨d, hd, -⟩) (rfl | ⟨d', hd', -⟩)
      · exact Or.inl (Matrix.mul_one 1)
      · simp at hd'
      · simp at hd
      · simp at hd)
    (by intro z; simp)
    (by simp) (by simp) (by norm_num)
    (by
      intro v hv
      have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
      rw [h32, Nat.testBit_two_pow_sub_one]
      simp [hv])
    (by norm_num)
    (by
      intro v hv
      have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
      rw [h32, Nat.testBit_two_pow_sub_one]
      simp [hv])
    (by simp) (by simp)
    (by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_range]
      exact hij)
    (fun z hz _ _ => List.mem_range.2 (hX z hz)) (by simp)
  apply h0
  have e : (List.range 191).map (recAt RL) = RL := by
    rw [← hlen]
    exact map_range_getD RL
  rw [e]
  exact hW

end CFSG.KC.C7109

end
