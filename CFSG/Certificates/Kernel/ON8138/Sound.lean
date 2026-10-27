
module

public import Certificates.Data.Kernel.ON8138.Defs
public import CFSG.RankThree.Native.ONTripleAutSpBase

public section

namespace CFSG.KC.ON8138

open CFSG.RankThree.Native.ONTriple Matrix

theorem andK_eq (a b : Bool) : andK a b = (a && b) := by cases a <;> rfl

theorem orK_eq (a b : Bool) : orK a b = (a || b) := by cases a <;> rfl

theorem notK_eq (a : Bool) : notK a = !a := by cases a <;> rfl

theorem strictN_eq (x : Nat) (k : Nat → Bool) : strictN x k = k x := by cases x <;> rfl

theorem allK_succ (n : Nat) (f : Nat → Bool) : allK (n + 1) f = (allK n f && f n) := by
  rw [← andK_eq]
  rfl

theorem anyK_succ (n : Nat) (f : Nat → Bool) : anyK (n + 1) f = (anyK n f || f n) := by
  rw [← orK_eq]
  rfl

theorem allK_iff (n : Nat) (f : Nat → Bool) : allK n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    rw [allK_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h k hk
      · exact hn
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem anyK_iff (n : Nat) (f : Nat → Bool) : anyK n f = true ↔ ∃ k < n, f k = true := by
  induction n with
  | zero =>
    exact ⟨fun h => absurd (show false = true from h) Bool.false_ne_true,
      fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    rw [anyK_succ, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

theorem bitK_eq (m d : Nat) : bitK m d = m.testBit d := by
  have e : bitK m d = Nat.beq (1 &&& (m >>> d)) 1 := rfl
  rw [e, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> d) with h | h <;> rw [h] <;> rfl

theorem bitK_land (m m' d : Nat) : bitK (Nat.land m m') d = (bitK m d && bitK m' d) := by
  rw [bitK_eq, bitK_eq, bitK_eq]
  exact Nat.testBit_land m m' d

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl

theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem dg_eq (c k : Nat) : dg c k = c / 3 ^ k % 3 := rfl

theorem dg_lt (c k : Nat) : dg c k < 3 := Nat.mod_lt _ (by norm_num)

theorem sum_digits_lt {B : ℕ} (hB : 0 < B) (f : ℕ → ℕ) (hf : ∀ k, f k < B) (n : ℕ) :
    ∑ k ∈ Finset.range n, f k * B ^ k < B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := hf n
    have hp := pow_pos hB n
    have h1 : f n * B ^ n ≤ (B - 1) * B ^ n := Nat.mul_le_mul_right _ (by omega)
    have h2 : (B - 1) * B ^ n + B ^ n = B ^ n * B := by
      rw [mul_comm (B ^ n) B, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hB]
    omega

theorem sum_digits_dg {B : ℕ} (hB : 0 < B) (f : ℕ → ℕ) (hf : ∀ k, f k < B) {n m : ℕ}
    (hm : m < n) : (∑ k ∈ Finset.range n, f k * B ^ k) / B ^ m % B = f m := by
  induction n with
  | zero => exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · have hp : f n * B ^ n = f n * B ^ (n - m - 1) * B * B ^ m := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
        congr 2
        omega
      rw [hp, Nat.add_mul_div_right _ _ (pow_pos hB m), Nat.add_mul_mod_self_right]
      exact ih hm
    · rw [Nat.add_mul_div_right _ _ (pow_pos hB m),
        Nat.div_eq_of_lt (sum_digits_lt hB f hf m), Nat.zero_add, Nat.mod_eq_of_lt (hf m)]

theorem mod_pow_eq_sum (B a n : ℕ) :
    a % B ^ n = ∑ k ∈ Finset.range n, (a / B ^ k % B) * B ^ k := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih => rw [Nat.mod_pow_succ, ih, Finset.sum_range_succ, mul_comm (B ^ n)]

theorem mulK_rec (a b n : ℕ) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (ent a b k) (Nat.pow (nat_lit 3) k))) n : ℕ) =
      ∑ k ∈ Finset.range n, ent a b k * 3 ^ k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem mulK_eq (a b : ℕ) : mulK a b = ∑ k ∈ Finset.range 16, ent a b k * 3 ^ k :=
  mulK_rec a b 16

theorem ent_lt (a b k : ℕ) : ent a b k < 3 := Nat.mod_lt _ (by norm_num)

theorem mulK_lt (a b : ℕ) : mulK a b < 3 ^ 16 := by
  rw [mulK_eq]
  exact sum_digits_lt (by norm_num) _ (ent_lt a b) 16

theorem dg_mulK (a b : ℕ) {m : ℕ} (hm : m < 16) : dg (mulK a b) m = ent a b m := by
  rw [dg_eq, mulK_eq]
  exact sum_digits_dg (by norm_num) _ (ent_lt a b) hm

@[expose] noncomputable def decK (c : ℕ) : M4 := Matrix.of fun i j => ((dg c (4 * i.val + j.val) : ℕ) : ZMod 3)

theorem ent_eq (a b : ℕ) (i j : Fin 4) :
    ent a b (4 * i.val + j.val) = (dg a (4 * i.val) * dg b j.val +
      dg a (4 * i.val + 1) * dg b (4 + j.val) + (dg a (4 * i.val + 2) * dg b (8 + j.val) +
      dg a (4 * i.val + 3) * dg b (12 + j.val))) % 3 := by
  have h1 : (4 * i.val + j.val) / 4 = i.val := by omega
  have h2 : (4 * i.val + j.val) % 4 = j.val := by omega
  unfold ent
  simp only [nadd, nmul, ndiv, nmod, h1, h2]

theorem decK_mulK (a b : ℕ) : decK (mulK a b) = decK a * decK b := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four, decK, Matrix.of_apply,
    dg_mulK a b (by omega), ent_eq, ZMod.natCast_mod]
  simp only [decK, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 4) : ℕ) = 3 from rfl, Nat.cast_add, Nat.cast_mul]
  ring_nf

theorem dg_eq_of_decK {a b : ℕ} (h : decK a = decK b) {k : ℕ} (hk : k < 16) : dg a k = dg b k := by
  have e := congrFun (congrFun h ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
  simp only [decK, Matrix.of_apply, show 4 * (k / 4) + k % 4 = k by omega] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 e
  rwa [Nat.mod_eq_of_lt (dg_lt a k), Nat.mod_eq_of_lt (dg_lt b k)] at this

theorem decK_inj {a b : ℕ} (h : decK a = decK b) (ha : a < 3 ^ 16) (hb : b < 3 ^ 16) : a = b := by
  rw [← Nat.mod_eq_of_lt ha, ← Nat.mod_eq_of_lt hb, mod_pow_eq_sum 3, mod_pow_eq_sum 3]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := dg_eq_of_decK h (Finset.mem_range.1 hk)
  rw [dg_eq, dg_eq] at this
  rw [this]

theorem powK_succ (c k : ℕ) : powK c (k + 1) = mulK (powK c k) c := rfl

theorem decK_IK : decK IK = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem decK_powK (c k : ℕ) : decK (powK c k) = decK c ^ k := by
  induction k with
  | zero => exact decK_IK
  | succ k ih => rw [powK_succ, decK_mulK, ih, pow_succ]

theorem powK_lt (c k : ℕ) : powK c k < 3 ^ 16 := by
  cases k with
  | zero =>
    change IK < 3 ^ 16
    decide
  | succ k => exact mulK_lt _ _

theorem decK_M0K : decK M0K = matNM 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem decK_M1K : decK M1K = matNM 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem IK_lt : IK < 3 ^ 16 := by decide

theorem getD_lt {l : List ℕ} (h3 : ∀ x ∈ l, x < 3) (k : ℕ) : l.getD k 0 < 3 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => simp
  | some x => exact h3 x (List.mem_of_getElem? h)

theorem packL_eq (l : List ℕ) : packL l = ∑ k ∈ Finset.range l.length, l.getD k 0 * 3 ^ k := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have e : packL (x :: l) = x + 3 * packL l := rfl
    rw [e, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem decK_packL {l : List ℕ} (hl : l.length = 16) (h3 : ∀ x ∈ l, x < 3) :
    decK (packL l) = toM4 l := by
  ext i j
  rw [decK, toM4, Matrix.of_apply, Matrix.of_apply, dg_eq, packL_eq, hl,
    sum_digits_dg (by norm_num) _ (getD_lt h3) (by omega)]

theorem packL_lt {l : List ℕ} (hl : l.length = 16) (h3 : ∀ x ∈ l, x < 3) : packL l < 3 ^ 16 := by
  rw [packL_eq, hl]
  exact sum_digits_lt (by norm_num) _ (getD_lt h3) 16

theorem decK_bit (k : ℕ) :
    decK (Bool.rec (motive := fun _ => Nat) M1K M0K (Nat.beq k (nat_lit 0))) = matNM k := by
  cases k with
  | zero => exact decK_M0K
  | succ k =>
    rw [matNM_of_ne (Nat.succ_ne_zero k)]
    exact decK_M1K

theorem foldK_nil (a : ℕ) : foldK [] a = a := rfl

theorem foldK_cons (k : ℕ) (w : List ℕ) (a : ℕ) :
    foldK (k :: w) a =
      foldK w (mulK a (Bool.rec (motive := fun _ => Nat) M1K M0K (Nat.beq k (nat_lit 0)))) := by
  show (List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => ih (mulK a (Bool.rec (motive := fun _ => Nat) M1K M0K (Nat.beq k (nat_lit 0)))))
    (k :: w) a : Nat) = _
  rfl

theorem decK_foldK (w : List ℕ) (a : ℕ) :
    decK (foldK w a) = decK a * (w.map fun k => matNM k).prod := by
  induction w generalizing a with
  | nil => rw [foldK_nil, List.map_nil, List.prod_nil, Matrix.mul_one]
  | cons k w ih =>
    rw [foldK_cons, ih, decK_mulK, decK_bit, List.map_cons, List.prod_cons, Matrix.mul_assoc]

theorem dg_codeK {a b c d : ℕ} (ha : a < 81) (hb : b < 81) (hc : c < 81) (hd : d < 81)
    (i j : Fin 4) :
    dg (codeK a b c d) (4 * i.val + j.val) = (![a, b, c, d] i) / 3 ^ j.val % 3 := by
  rw [dg_eq]
  simp only [codeK, nadd, nmul]
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem decK_codeK {a b c d : ℕ} (ha : a < 81) (hb : b < 81) (hc : c < 81) (hd : d < 81) :
    decK (codeK a b c d) = Matrix.of ![vdec a, vdec b, vdec c, vdec d] := by
  ext i j
  rw [decK, Matrix.of_apply, dg_codeK ha hb hc hd, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [vdec]

theorem tp_expand (e f : Fin 4 → ZMod 3) : ThreeQRel.threePair omegaZ e f =
    e 0 * f 3 + 2 * (e 1 * f 2) + 2 * (e 1 * f 3) + e 2 * f 1 + 2 * (e 3 * f 0) + e 3 * f 1 := by
  have h : ∀ i j, omegaZ i j = (omegaN i j : ZMod 3) := fun _ _ => rfl
  simp only [ThreeQRel.threePair, ThreeQRel.threeForm, Fin.sum_univ_four, h]
  simp [omegaN]
  ring

theorem tp_self (e : Fin 4 → ZMod 3) : ThreeQRel.threePair omegaZ e e = 0 := by
  rw [tp_expand]
  have h3 : (3 : ZMod 3) = 0 := rfl
  linear_combination (e 0 * e 3 + e 1 * e 2 + e 1 * e 3) * h3

theorem tp_swap (e f : Fin 4 → ZMod 3) :
    ThreeQRel.threePair omegaZ f e = -ThreeQRel.threePair omegaZ e f := by
  have h3 : ∀ x : ZMod 3, 3 * x = 0 := fun x => by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hs : ThreeQRel.threePair omegaZ f e + ThreeQRel.threePair omegaZ e f =
      3 * (e 0 * f 3 + e 1 * f 2 + e 1 * f 3 + e 2 * f 1 + e 3 * f 0 + e 3 * f 1) := by
    rw [tp_expand, tp_expand]
    ring
  rw [h3] at hs
  exact eq_neg_of_add_eq_zero_left hs

theorem pairK_eq (x y : ℕ) : pairK x y = (ThreeQRel.threePair omegaZ (vdec x) (vdec y)).val := by
  rw [tp_expand]
  have hv : ∀ z : ℕ, vdec z 0 = ((vd z 0 : ℕ) : ZMod 3) ∧ vdec z 1 = ((vd z 1 : ℕ) : ZMod 3) ∧
      vdec z 2 = ((vd z 2 : ℕ) : ZMod 3) ∧ vdec z 3 = ((vd z 3 : ℕ) : ZMod 3) := by
    intro z
    simp [vdec, vd, dg_eq]
  obtain ⟨x0, x1, x2, x3⟩ := hv x
  obtain ⟨y0, y1, y2, y3⟩ := hv y
  rw [x0, x1, x2, x3, y0, y1, y2, y3]
  simp only [pairK, nadd, nmul, nmod]
  rw [← ZMod.val_natCast]
  congr 1
  push_cast
  ring

theorem decA_OmA_apply (i j : Fin 4) : decA OmA i j = omegaZ i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem omA_mul_omInvA : decA OmA * decA OmInvA = 1 := by
  rw [← decA_amul, ← decA_idA]
  congr 1

theorem mul_omega_apply (T : M4) (i j : Fin 4) :
    (T * decA OmA * T.transpose) i j = ThreeQRel.threePair omegaZ (T i) (T j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ThreeQRel.threePair, ThreeQRel.threeForm,
    decA_OmA_apply, Finset.sum_mul]

theorem mul_symInvM {T : M4}
    (hT : ∀ i j, ThreeQRel.threePair omegaZ (T i) (T j) = omegaZ i j) : T * symInvM T = 1 := by
  have h : T * decA OmA * T.transpose = decA OmA := by
    ext i j
    rw [mul_omega_apply, hT, decA_OmA_apply]
  rw [symInvM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, omA_mul_omInvA]

theorem val_eq {x : ZMod 3} {v : ℕ} (h : x.val = v) : x = v := by
  rw [← h, ZMod.natCast_zmod_val]

theorem tp_lower {e f : Fin 4 → ZMod 3} {v : ℕ} {w : ZMod 3}
    (h : (ThreeQRel.threePair omegaZ e f).val = v) (hw : -((v : ℕ) : ZMod 3) = w) :
    ThreeQRel.threePair omegaZ f e = w := by
  rw [tp_swap, val_eq h, hw]

theorem symp_of_pairs {T : M4}
    (h01 : (ThreeQRel.threePair omegaZ (T 0) (T 1)).val = 0)
    (h02 : (ThreeQRel.threePair omegaZ (T 0) (T 2)).val = 0)
    (h12 : (ThreeQRel.threePair omegaZ (T 1) (T 2)).val = 2)
    (h03 : (ThreeQRel.threePair omegaZ (T 0) (T 3)).val = 1)
    (h13 : (ThreeQRel.threePair omegaZ (T 1) (T 3)).val = 2)
    (h23 : (ThreeQRel.threePair omegaZ (T 2) (T 3)).val = 0) :
    ∀ i j, ThreeQRel.threePair omegaZ (T i) (T j) = omegaZ i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact (tp_self _).trans (by decide)
  · exact (val_eq h01).trans (by decide)
  · exact (val_eq h02).trans (by decide)
  · exact (val_eq h03).trans (by decide)
  · exact tp_lower h01 (by decide)
  · exact (tp_self _).trans (by decide)
  · exact (val_eq h12).trans (by decide)
  · exact (val_eq h13).trans (by decide)
  · exact tp_lower h02 (by decide)
  · exact tp_lower h12 (by decide)
  · exact (tp_self _).trans (by decide)
  · exact (val_eq h23).trans (by decide)
  · exact tp_lower h03 (by decide)
  · exact tp_lower h13 (by decide)
  · exact tp_lower h23 (by decide)
  · exact (tp_self _).trans (by decide)

end CFSG.KC.ON8138

end
