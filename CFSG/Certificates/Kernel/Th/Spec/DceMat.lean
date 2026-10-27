module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.F2WordSound
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th

@[expose] def toMat (A : ℕ) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  Matrix.of fun i j => ((A.testBit (24 * (i : ℕ) + j)).toNat : ZMod 2)

@[expose] def toVec (x : ℕ) : Fin 24 → ZMod 2 := fun j => ((x.testBit j).toNat : ZMod 2)

theorem cast_xor (a b : Bool) : (((a ^^ b).toNat : ℕ) : ZMod 2) = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide

theorem cast_and (a b : Bool) : (((a && b).toNat : ℕ) : ZMod 2) = a.toNat * b.toNat := by
  cases a <;> cases b <;> decide

theorem eq_of_cast_eq {a b : Bool} (h : ((a.toNat : ℕ) : ZMod 2) = b.toNat) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem cast_recXor (f : ℕ → Bool) : ∀ n : ℕ,
    (((Nat.rec (motive := fun _ => Bool) false (fun k b => f k ^^ b) n : Bool).toNat : ℕ) :
      ZMod 2) = ∑ k : Fin n, ((f k).toNat : ZMod 2)
  | 0 => by simp
  | n + 1 => by
    rw [Fin.sum_univ_castSucc]
    change (((f n ^^ Nat.rec (motive := fun _ => Bool) false (fun k b => f k ^^ b) n).toNat : ℕ) :
      ZMod 2) = _
    rw [cast_xor, cast_recXor f n, add_comm]
    simp

set_option exponentiation.threshold 700

theorem rowMask_eq : rowMask = 2 ^ 24 - 1 := rfl

theorem ident24_lt : ident24 < 2 ^ 576 := by decide +kernel

theorem ident24_testBit : ∀ i < 24, ∀ j < 24, ident24.testBit (24 * i + j) = decide (i = j) := by
  decide +kernel

theorem testBit_lt_576 {A : ℕ} (hA : A < 2 ^ 576) {p : ℕ} (hp : 576 ≤ p) : A.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hp))

theorem rR_eq : Nat.div (KLie.CT.maskN (Nat.mul 24 24)) (KLie.CT.maskN 24) = c0 := by
  decide +kernel

theorem rF_eq : KLie.CT.maskN 24 = rowMask := by decide +kernel

theorem mul24_eq_mulW (A B : ℕ) : mul24 A B = F2W.mulW 24 A B := by
  rw [F2W.mulW_eq_rec, rR_eq, rF_eq]
  rfl

theorem mul24_eq_mulF (A B : ℕ) : mul24 A B = M1F2.mulF 24 A B := by
  rw [mul24_eq_mulW, F2W.mulW_eq]

theorem mul24_lt (A B : ℕ) : mul24 A B < 2 ^ 576 := by
  rw [mul24_eq_mulF, F2W.mulF_eq_orN]
  exact F2W.orN_fields_lt fun i _ => F2W.vmF_lt 24 B _

theorem testBit_mul24 (A B : ℕ) {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    (mul24 A B).testBit (24 * i + j) =
      Nat.rec (motive := fun _ => Bool) false
        (fun k b => (A.testBit (24 * i + k) && B.testBit (24 * k + j)) ^^ b) 24 := by
  rw [mul24_eq_mulF, F2W.mulF_eq_orN,
    F2W.testBit_orN_fields fun i _ => F2W.vmF_lt 24 B (M1F2.rowF 24 A i)]
  have hq : (24 * i + j) / 24 = i := by omega
  have hr : (24 * i + j) % 24 = j := by omega
  have hd : decide (24 * i + j < 24 * 24) = true := decide_eq_true (by omega)
  rw [hq, hr, hd, Bool.true_and, F2W.testBit_vmF 24 B _ _ hj]
  refine F2W.rec_congr
    (F := fun k b => ((M1F2.rowF 24 A i).testBit k && B.testBit (k * 24 + j)) ^^ b)
    (G := fun k b => (A.testBit (24 * i + k) && B.testBit (24 * k + j)) ^^ b)
    false 24 fun k hk b => ?_
  rw [F2W.testBit_rowF 24 A i k hk, Nat.mul_comm i 24, Nat.mul_comm k 24]

theorem toMat_mul24 (A B : ℕ) : toMat (mul24 A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.mul_apply]
  rw [testBit_mul24 A B i.2 j.2, cast_recXor]
  exact Finset.sum_congr rfl fun k _ => cast_and _ _

theorem toMat_ident24 : toMat ident24 = 1 := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.one_apply]
  rw [ident24_testBit i i.2 j j.2]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Fin.val_inj]

theorem eq_of_toMat_eq {A B : ℕ} (hA : A < 2 ^ 576) (hB : B < 2 ^ 576) (h : toMat A = toMat B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 576
  · have h' := congrFun (congrFun h ⟨p / 24, by omega⟩) ⟨p % 24, Nat.mod_lt _ (by omega)⟩
    simp only [toMat, Matrix.of_apply, Nat.div_add_mod] at h'
    exact eq_of_cast_eq h'
  · rw [testBit_lt_576 hA (by omega), testBit_lt_576 hB (by omega)]

theorem eq_of_toVec_eq {x y : ℕ} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) (h : toVec x = toVec y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 24
  · exact eq_of_cast_eq (congrFun h ⟨p, hp⟩)
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem mul24_assoc (A B C : ℕ) : mul24 (mul24 A B) C = mul24 A (mul24 B C) :=
  eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) (by simp only [toMat_mul24, Matrix.mul_assoc])

theorem ident24_mul24 {A : ℕ} (hA : A < 2 ^ 576) : mul24 ident24 A = A :=
  eq_of_toMat_eq (mul24_lt _ _) hA (by rw [toMat_mul24, toMat_ident24, Matrix.one_mul])

theorem mul24_ident24 {A : ℕ} (hA : A < 2 ^ 576) : mul24 A ident24 = A :=
  eq_of_toMat_eq (mul24_lt _ _) hA (by rw [toMat_mul24, toMat_ident24, Matrix.mul_one])

theorem spG_or (a b s x y : ℕ) :
    Nat.lor (Nat.land (x ||| y) a) (Nat.shiftLeft (Nat.land (x ||| y) b) s) =
      Nat.lor (Nat.land x a) (Nat.shiftLeft (Nat.land x b) s) |||
        Nat.lor (Nat.land y a) (Nat.shiftLeft (Nat.land y b) s) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change ((x ||| y) &&& a ||| ((x ||| y) &&& b) <<< s).testBit p =
    ((x &&& a ||| (x &&& b) <<< s) ||| (y &&& a ||| (y &&& b) <<< s)).testBit p
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
  cases x.testBit p <;> cases y.testBit p <;> cases a.testBit p <;> cases decide (p ≥ s) <;>
    cases x.testBit (p - s) <;> cases y.testBit (p - s) <;> cases b.testBit (p - s) <;> rfl

theorem spG3_or (a b c s t x y : ℕ) :
    Nat.lor (Nat.lor (Nat.land (x ||| y) a) (Nat.shiftLeft (Nat.land (x ||| y) b) s))
      (Nat.shiftLeft (Nat.land (x ||| y) c) t) =
      Nat.lor (Nat.lor (Nat.land x a) (Nat.shiftLeft (Nat.land x b) s))
        (Nat.shiftLeft (Nat.land x c) t) |||
      Nat.lor (Nat.lor (Nat.land y a) (Nat.shiftLeft (Nat.land y b) s))
        (Nat.shiftLeft (Nat.land y c) t) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change (((x ||| y) &&& a ||| ((x ||| y) &&& b) <<< s) ||| ((x ||| y) &&& c) <<< t).testBit p =
    ((((x &&& a ||| (x &&& b) <<< s) ||| (x &&& c) <<< t)) |||
      (((y &&& a ||| (y &&& b) <<< s) ||| (y &&& c) <<< t))).testBit p
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
  cases x.testBit p <;> cases y.testBit p <;> cases a.testBit p <;> cases decide (p ≥ s) <;>
    cases x.testBit (p - s) <;> cases y.testBit (p - s) <;> cases b.testBit (p - s) <;>
    cases decide (p ≥ t) <;> cases x.testBit (p - t) <;> cases y.testBit (p - t) <;>
    cases c.testBit (p - t) <;> rfl

@[expose] noncomputable def chain (y : ℕ) : ℕ := sp4 (sp3 (sp2 (sp1 y)))

theorem sp1_or (x y : ℕ) : sp1 (x ||| y) = sp1 x ||| sp1 y := spG_or _ _ _ x y
theorem sp2_or (x y : ℕ) : sp2 (x ||| y) = sp2 x ||| sp2 y := spG_or _ _ _ x y
theorem sp3_or (x y : ℕ) : sp3 (x ||| y) = sp3 x ||| sp3 y := spG_or _ _ _ x y
theorem sp4_or (x y : ℕ) : sp4 (x ||| y) = sp4 x ||| sp4 y := spG3_or _ _ _ _ _ x y

theorem chain_or (x y : ℕ) : chain (x ||| y) = chain x ||| chain y := by
  simp only [chain, sp1_or, sp2_or, sp3_or, sp4_or]

theorem chain_zero : chain 0 = 0 := rfl

theorem chain_pow : ∀ i < 24, chain (1 <<< i) = 1 <<< (24 * i) := by decide +kernel

theorem orN_congr {f g : ℕ → ℕ} : ∀ n : ℕ, (∀ i < n, f i = g i) →
    KLie.CT.orN n f = KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [F2W.orN_succ, F2W.orN_succ, orN_congr n fun i hi => h i (by omega), h n (by omega)]

theorem chain_orN (f : ℕ → ℕ) : ∀ n : ℕ,
    chain (KLie.CT.orN n f) = KLie.CT.orN n fun i => chain (f i)
  | 0 => chain_zero
  | n + 1 => by rw [F2W.orN_succ, F2W.orN_succ, chain_or, chain_orN f n]

theorem eq_orN_bits {y : ℕ} (hy : y < 2 ^ 24) :
    y = KLie.CT.orN 24 fun i => (y.testBit i).toNat <<< (1 * i) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [F2W.testBit_orN_fields fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega),
    Nat.div_one, Nat.mod_one, Nat.one_mul]
  by_cases hp : p < 24
  · cases y.testBit p <;> simp [hp]
  · simp [hp, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega)
      (Nat.le_of_not_lt hp)))]

theorem chain_eq {y : ℕ} (hy : y < 2 ^ 24) :
    chain y = KLie.CT.orN 24 fun i => (y.testBit i).toNat <<< (24 * i) := by
  conv_lhs => rw [eq_orN_bits hy]
  rw [chain_orN]
  refine orN_congr 24 fun i hi => ?_
  cases y.testBit i
  · simp only [Bool.toNat_false, Nat.zero_shiftLeft]
    exact chain_zero
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact chain_pow i hi

theorem testBit_spreadS {y : ℕ} (hy : y < 2 ^ 24) (r : ℕ) {j : ℕ} (hj : j < 24) :
    (spreadS y).testBit (24 * r + j) = (decide (r < 24) && y.testBit r) := by
  change (Nat.mul (chain y) rowMask).testBit _ = _
  have h1 : ∀ i < 24, (y.testBit i).toNat < 2 ^ 24 :=
    fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega)
  rw [chain_eq hy, rowMask_eq]
  change ((KLie.CT.orN 24 fun i => (y.testBit i).toNat <<< (24 * i)) * (2 ^ 24 - 1)).testBit _ = _
  rw [F2W.orN_fields_mul h1 fun _ _ => F2W.toNat_mul_lt _,
    F2W.testBit_orN_fields fun _ _ => F2W.toNat_mul_lt _]
  have hq : (24 * r + j) / 24 = r := by omega
  have hr : (24 * r + j) % 24 = j := by omega
  rw [hq, hr]
  have hd : decide (24 * r + j < 24 * 24) = decide (r < 24) := by
    by_cases h : r < 24
    · simp [h]; omega
    · simp [h]; omega
  rw [hd]
  cases y.testBit r
  · simp
  · rw [Bool.toNat_true, Nat.one_mul, Nat.testBit_two_pow_sub_one]
    simp [hj]

theorem testBit_fold1 (t r j : ℕ) :
    (fold1 t).testBit (24 * r + j) = (t.testBit (24 * r + j) ^^ t.testBit (24 * (r + 12) + j)) := by
  change (t ^^^ (t >>> 288)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  have h : 288 + (24 * r + j) = 24 * (r + 12) + j := by ring
  rw [h]

theorem testBit_fold2 (t r j : ℕ) :
    (fold2 t).testBit (24 * r + j) = (t.testBit (24 * r + j) ^^ t.testBit (24 * (r + 6) + j)) := by
  change (t ^^^ (t >>> 144)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  have h : 144 + (24 * r + j) = 24 * (r + 6) + j := by ring
  rw [h]

theorem testBit_fold3 (t r j : ℕ) :
    (fold3 t).testBit (24 * r + j) = (t.testBit (24 * r + j) ^^ t.testBit (24 * (r + 3) + j)) := by
  change (t ^^^ (t >>> 72)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  have h : 72 + (24 * r + j) = 24 * (r + 3) + j := by ring
  rw [h]

theorem testBit_fold45 (t r j : ℕ) :
    (fold45 t).testBit (24 * r + j) = (t.testBit (24 * r + j) ^^
      (t.testBit (24 * (r + 1) + j) ^^ t.testBit (24 * (r + 2) + j))) := by
  change (t ^^^ ((t >>> 24) ^^^ (t >>> 48))).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have h1 : 24 + (24 * r + j) = 24 * (r + 1) + j := by ring
  have h2 : 48 + (24 * r + j) = 24 * (r + 2) + j := by ring
  rw [h1, h2]

theorem testBit_T (x M r : ℕ) {j : ℕ} (hj : j < 24) (hx : x < 2 ^ 24) :
    (Nat.land (spreadS x) M).testBit (24 * r + j) =
      (decide (r < 24) && (x.testBit r && M.testBit (24 * r + j))) := by
  change (spreadS x &&& M).testBit _ = _
  rw [Nat.testBit_and, testBit_spreadS hx r hj]
  by_cases h : r < 24 <;> simp [h]

theorem rowMask_testBit {j : ℕ} (hj : j < 24) : rowMask.testBit j = true := by
  rw [rowMask_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem vecmul_lt (x M : ℕ) : vecmul x M < 2 ^ 24 :=
  Nat.lt_of_le_of_lt Nat.and_le_right
    (by rw [rowMask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem cast_testBit_vecmul {x : ℕ} (hx : x < 2 ^ 24) (M : ℕ) {j : ℕ} (hj : j < 24) :
    (((vecmul x M).testBit j).toNat : ZMod 2) =
      ∑ k : Fin 24, ((x.testBit k).toNat : ZMod 2) * (M.testBit (24 * k + j)).toNat := by
  change ((((fold45 (fold3 (fold2 (fold1 (Nat.land (spreadS x) M)))) &&& rowMask).testBit j).toNat :
    ℕ) : ZMod 2) = _
  have h0 : j = 24 * 0 + j := by omega
  rw [Nat.testBit_and, rowMask_testBit hj, Bool.and_true]
  conv_lhs => rw [h0]
  simp only [testBit_fold45, testBit_fold3, testBit_fold2, testBit_fold1, testBit_T x M _ hj hx,
    cast_xor, cast_and, Nat.reduceAdd, -Nat.reduceMul, Nat.reduceLT, decide_true, decide_false,
    Bool.true_and, Bool.false_and, Bool.toNat_false, Nat.cast_zero, add_zero, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((x.testBit k).toNat : ZMod 2) *
    (M.testBit (24 * k + j)).toNat) 24]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem toVec_vecmul {x : ℕ} (hx : x < 2 ^ 24) (M : ℕ) :
    toVec (vecmul x M) = Matrix.vecMul (toVec x) (toMat M) := by
  funext j
  simp only [toVec, toMat, Matrix.vecMul, dotProduct, Matrix.of_apply]
  exact cast_testBit_vecmul hx M j.2

open KLie.CT in
theorem col_eqN {d : ℕ} (hd : 0 < d) (n A k : ℕ) :
    (A >>> k) &&& (orN n fun i => 1 <<< (d * i)) =
      orN n fun i => (A.testBit (d * i + k)).toNat <<< (d * i) := by
  have h1 : ∀ i < n, (1 : Nat) < 2 ^ d := fun _ _ => Nat.one_lt_two_pow (by omega)
  have h2 : ∀ i < n, (A.testBit (d * i + k)).toNat < 2 ^ d := fun i hi =>
    Nat.lt_of_le_of_lt (Bool.toNat_le _) (h1 i hi)
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, F2W.testBit_orN_fields h1, F2W.testBit_orN_fields h2,
    Nat.testBit_shiftRight, F2W.testBit_one_eq, Nat.add_comm k p]
  by_cases hp : p % d = 0
  · have hpd : d * (p / d) = p := by have := Nat.div_add_mod p d; omega
    rw [hp, hpd]
    cases A.testBit (p + k) <;> simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp
    rw [hj]
    cases (A.testBit (d * (p / d) + k)) <;> simp [Nat.testBit_succ]

open KLie.CT in
theorem testBit_termN {d : ℕ} (hd : 0 < d) (n A B k p : ℕ) :
    ((((A >>> k) &&& (orN n fun i => 1 <<< (d * i))) * (2 ^ d - 1)) &&&
      (((B >>> (d * k)) &&& (2 ^ d - 1)) * (orN n fun i => 1 <<< (d * i)))).testBit p =
      (decide (p < d * n) && (A.testBit (d * (p / d) + k) && B.testBit (d * k + p % d))) := by
  have h1 : ∀ i < n, (1 : Nat) < 2 ^ d := fun _ _ => Nat.one_lt_two_pow (by omega)
  have hrow : (B >>> (d * k)) &&& (2 ^ d - 1) < 2 ^ d := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos d)
  rw [col_eqN hd, F2W.orN_fields_mul
    (fun i hi => Nat.lt_of_le_of_lt (Bool.toNat_le _) (h1 i hi))
    (fun _ _ => F2W.toNat_mul_lt _), Nat.mul_comm _ (orN n _)]
  have hb := F2W.orN_fields_mul (c := (B >>> (d * k)) &&& (2 ^ d - 1)) (f := fun _ => 1) h1
    (fun _ _ => by rw [Nat.one_mul]; exact hrow)
  simp only [Nat.one_mul] at hb
  rw [hb, Nat.testBit_and, F2W.testBit_orN_fields (fun _ _ => F2W.toNat_mul_lt _),
    F2W.testBit_orN_fields (fun _ _ => hrow)]
  have hm := Nat.mod_lt p hd
  have hF : ((A.testBit (d * (p / d) + k)).toNat * (2 ^ d - 1)).testBit (p % d) =
      A.testBit (d * (p / d) + k) := by
    cases A.testBit (d * (p / d) + k) <;> simp [hm]
  rw [hF, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  cases decide (p < d * n) <;> simp [hm]

open KLie.CT in
theorem sel_eq (n : ℕ) :
    Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 24 n)) 1) 16777215 =
      orN n fun i => 1 <<< (24 * i) := by
  have h1 : ∀ i < n, (1 : Nat) < 2 ^ 24 := fun _ _ => by omega
  have hm : (orN n fun i => 1 <<< (24 * i)) * (2 ^ 24 - 1) = 2 ^ (24 * n) - 1 := by
    have h := F2W.orN_fields_mul (c := 2 ^ 24 - 1) (f := fun _ => 1) h1
      (fun _ _ => by rw [Nat.one_mul]; omega)
    simp only [Nat.one_mul] at h
    rw [h]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [F2W.testBit_orN_fields (fun _ _ => by omega), Nat.testBit_two_pow_sub_one,
      Nat.testBit_two_pow_sub_one]
    simp [Nat.mod_lt p (show 0 < 24 by omega)]
  have hpos : 0 < 2 ^ 24 - 1 := by omega
  have e : Nat.shiftLeft 1 (Nat.mul 24 n) = 2 ^ (24 * n) := by
    change 1 <<< (24 * n) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have e2 : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [e, e2]
  change (2 ^ (24 * n) - 1) / (2 ^ 24 - 1) = _
  rw [← hm, Nat.mul_div_cancel _ hpos]

theorem mulRows_eq_rec (c X B : ℕ) : mulRows c X B =
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc ^^^
      ((((X >>> k) &&& c) * rowMask) &&& (((B >>> (24 * k)) &&& rowMask) * c))) 24 := rfl

open KLie.CT in
theorem testBit_mulRows (n X B p : ℕ) :
    (mulRows (orN n fun i => 1 <<< (24 * i)) X B).testBit p =
      (decide (p < 24 * n) && Nat.rec (motive := fun _ => Bool) false
        (fun k b => (X.testBit (24 * (p / 24) + k) && B.testBit (24 * k + p % 24)) ^^ b) 24) := by
  rw [mulRows_eq_rec, rowMask_eq, F2W.testBit_xorRec]
  simp only [testBit_termN (show 0 < 24 by omega)]
  by_cases hp : p < 24 * n
  · simp only [hp, decide_true, Bool.true_and]
    refine F2W.rec_congr
      (F := fun k b => b ^^ (X.testBit (24 * (p / 24) + k) && B.testBit (24 * k + p % 24)))
      (G := fun k b => (X.testBit (24 * (p / 24) + k) && B.testBit (24 * k + p % 24)) ^^ b)
      false 24 fun k _ b => ?_
    rw [Bool.xor_comm]
  · simp only [hp, decide_false, Bool.false_and]
    exact F2W.rec_xor_false 24

theorem testBit_rowOf (P i j : ℕ) :
    (rowOf P i).testBit j = (decide (j < 24) && P.testBit (24 * i + j)) := by
  change ((P >>> (24 * i)) &&& rowMask).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, rowMask_eq, Nat.testBit_two_pow_sub_one,
    Nat.add_comm (24 * i) j]
  cases decide (j < 24) <;> simp

theorem rowOf_lt (P i : ℕ) : rowOf P i < 2 ^ 24 :=
  Nat.lt_of_le_of_lt Nat.and_le_right
    (by rw [rowMask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem toVec_rowOf_mulRows (n X B : ℕ) {i : ℕ} (hi : i < n) :
    toVec (rowOf (mulRows (KLie.CT.orN n fun i => 1 <<< (24 * i)) X B) i) =
      Matrix.vecMul (toVec (rowOf X i)) (toMat B) := by
  funext j
  simp only [toVec, toMat, Matrix.vecMul, dotProduct, Matrix.of_apply]
  rw [testBit_rowOf, testBit_mulRows]
  have hj := j.2
  have hd : decide ((j : ℕ) < 24) = true := decide_eq_true hj
  have hq : (24 * i + j) / 24 = i := by omega
  have hr : (24 * i + j) % 24 = j := by omega
  have hn : decide (24 * i + (j : ℕ) < 24 * n) = true := decide_eq_true (by omega)
  rw [hd, Bool.true_and, hq, hr, hn, Bool.true_and, cast_recXor]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cast_and, testBit_rowOf]
  have hk : decide ((k : ℕ) < 24) = true := decide_eq_true k.2
  rw [hk, Bool.true_and]

theorem mulRows_zero_right (n X : ℕ) :
    mulRows (KLie.CT.orN n fun i => 1 <<< (24 * i)) X 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_mulRows, Nat.zero_testBit]
  have : Nat.rec (motive := fun _ => Bool) false
      (fun k b => (X.testBit (24 * (p / 24) + k) && (0 : ℕ).testBit (24 * k + p % 24)) ^^ b) 24
        = false := by
    simp only [Nat.zero_testBit, Bool.and_false, Bool.false_xor]
    exact F2W.rec_xor_false 24
  rw [this]; simp

@[expose] def tauIdx (tau i : ℕ) : ℕ := Nat.land (Nat.shiftRight tau (Nat.mul 7 i)) 127

theorem permRows_succ (X tau n : ℕ) : permRows X tau (n + 1) =
    Nat.lor (permRows X tau n) (Nat.shiftLeft (Nat.land (Nat.shiftRight X
      (Nat.mul 24 (tauIdx tau n))) rowMask) (Nat.mul 24 n)) := rfl

theorem testBit_permRows (X tau : ℕ) : ∀ n p : ℕ, (permRows X tau n).testBit p =
    (decide (p < 24 * n) && X.testBit (24 * tauIdx tau (p / 24) + p % 24))
  | 0, p => by simp [permRows]
  | n + 1, p => by
    rw [permRows_succ]
    change ((permRows X tau n) ||| ((X >>> (24 * tauIdx tau n)) &&& rowMask) <<< (24 * n)).testBit p
      = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_permRows X tau n p, Nat.testBit_and,
      Nat.testBit_shiftRight, rowMask_eq, Nat.testBit_two_pow_sub_one]
    by_cases h1 : p < 24 * n
    · have h2 : ¬ p ≥ 24 * n := by omega
      have h3 : p < 24 * (n + 1) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : p < 24 * (n + 1)
      · have hq : p / 24 = n := by omega
        have hr : p - 24 * n = p % 24 := by omega
        have hr2 : p % 24 < 24 := Nat.mod_lt _ (by omega)
        have hp3 : p ≥ 24 * n := by omega
        simp [h1, h2, hp3, hq, hr, hr2, Nat.add_comm (24 * tauIdx tau n)]
      · have hp3 : p ≥ 24 * n := by omega
        have hr2 : ¬ p - 24 * n < 24 := by omega
        simp [h1, h2, hp3, hr2]

theorem rowOf_permRows (X tau n : ℕ) {i : ℕ} (hi : i < n) :
    rowOf (permRows X tau n) i = rowOf X (tauIdx tau i) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowOf, testBit_rowOf, testBit_permRows]
  by_cases hj : j < 24
  · have hq : (24 * i + j) / 24 = i := by omega
    have hr : (24 * i + j) % 24 = j := by omega
    have hn : decide (24 * i + j < 24 * n) = true := decide_eq_true (by omega)
    simp [hj, hq, hr, hn]
  · simp [hj]

theorem permRows_lt (X tau n : ℕ) : permRows X tau n < 2 ^ (24 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  rw [testBit_permRows]
  have : ¬ p < 24 * n := by omega
  simp [this]

theorem mulRows_lt (n X B : ℕ) :
    mulRows (KLie.CT.orN n fun i => 1 <<< (24 * i)) X B < 2 ^ (24 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro p hp
  rw [testBit_mulRows]
  have : ¬ p < 24 * n := by omega
  simp [this]

theorem rowOf_eq_zero_of_lt {Y n : ℕ} (hY : Y < 2 ^ (24 * n)) {t : ℕ} (ht : n ≤ t) :
    rowOf Y t = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowOf, Nat.zero_testBit]
  have : Y.testBit (24 * t + j) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by omega) (by omega)))
  rw [this]; simp

abbrev Mat24 : Type := Matrix (Fin 24) (Fin 24) (ZMod 2)

@[expose] noncomputable def ptS (n P : ℕ) : Finset (Fin 24 → ZMod 2) :=
  (Finset.range n).image fun i => toVec (rowOf P i)

@[expose] def actP (S : Finset (Fin 24 → ZMod 2)) (y : Mat24ˣ) : Finset (Fin 24 → ZMod 2) :=
  S.image fun v => Matrix.vecMul v (y : Mat24)

theorem actP_one (S : Finset (Fin 24 → ZMod 2)) : actP S 1 = S := by
  unfold actP
  simp only [Units.val_one, Matrix.vecMul_one, Finset.image_id']

theorem actP_mul (S : Finset (Fin 24 → ZMod 2)) (a b : Mat24ˣ) :
    actP (actP S a) b = actP S (a * b) := by
  unfold actP
  rw [Finset.image_image]
  refine Finset.image_congr fun v _ => ?_
  simp only [Function.comp_apply, Units.val_mul, Matrix.vecMul_vecMul]


theorem andB_iff {a b : Bool} : CFSG.KC.Th.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff {a b : Bool} : CFSG.KC.Th.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem notB_iff {b : Bool} : DceS.notB b = true ↔ b = false := by
  cases b <;> decide

theorem allB_iff (f : ℕ → Bool) : ∀ m : ℕ,
    Nat.rec (motive := fun _ => Bool) true (fun i acc => CFSG.KC.Th.andB acc (f i)) m = true ↔
      ∀ i < m, f i = true
  | 0 => by simp
  | m + 1 => by
    change CFSG.KC.Th.andB (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => CFSG.KC.Th.andB acc (f i)) m) (f m) = true ↔ _
    rw [andB_iff, allB_iff f m]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem rowsOK_spec {n P : ℕ} (h : rowsOK n P = true) :
    0 < rowOf P 0 ∧ ∀ i, i + 1 < n → rowOf P i < rowOf P (i + 1) := by
  unfold rowsOK at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  refine ⟨Nat.blt_eq.mp h1, fun i hi => ?_⟩
  have := (allB_iff (fun i => Nat.blt (rowOf P i) (rowOf P (Nat.succ i))) _).1 h2 i (by
    change i < n - 1
    omega)
  exact Nat.blt_eq.mp this

theorem rows_pos_mono {n P : ℕ} (h : rowsOK n P = true) (hn : 0 < n) :
    (∀ i < n, 0 < rowOf P i) ∧ ∀ i j, i < j → j < n → rowOf P i < rowOf P j := by
  obtain ⟨h0, hinc⟩ := rowsOK_spec h
  have hmono : ∀ i j, i < j → j < n → rowOf P i < rowOf P j := by
    intro i j hij
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact (ih hij (by omega)).trans (hinc j hj)
      · exact hinc i hj
  refine ⟨fun i hi => ?_, hmono⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact h0
  · exact h0.trans (hmono 0 i hi0 hi)

theorem eq_of_rows_eq {n P Q : ℕ} (hP : P < 2 ^ (24 * n)) (hQ : Q < 2 ^ (24 * n))
    (h : ∀ i < n, rowOf P i = rowOf Q i) : P = Q := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 24 * n
  · have hi : p / 24 < n := by omega
    have e := congrArg (fun r => r.testBit (p % 24)) (h (p / 24) hi)
    simp only [testBit_rowOf] at e
    have h1 : decide (p % 24 < 24) = true := decide_eq_true (Nat.mod_lt _ (by omega))
    have h2 : 24 * (p / 24) + p % 24 = p := Nat.div_add_mod p 24
    rw [h1, h2] at e
    simpa using e
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hQ (Nat.pow_le_pow_right
      (by omega) (by omega)))]

theorem rowOf_zero_eq {P : ℕ} (hP : P < 2 ^ 24) : rowOf P 0 = P := by
  change (P >>> (24 * 0)) &&& rowMask = P
  rw [rowMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt hP]

theorem actOK_sound {n sel P M Q tau : ℕ} (hsel : DceS.selOK n sel = true)
    (hQ : n = 1 ∨ rowsOK n Q = true) (hP : P < 2 ^ (24 * n))
    (h : DceS.actOK n sel P M Q tau = true) (y : Mat24ˣ) (hy : (y : Mat24) = toMat M) :
    actP (ptS n P) y = ptS n Q := by
  unfold DceS.actOK at h
  cases hn : Nat.beq n 1
  · rw [hn] at h
    have hn1 : n ≠ 1 := fun e => by rw [e] at hn; exact absurd hn (by decide)
    have hQ' : rowsOK n Q = true := hQ.resolve_left hn1
    have h' : chkAct sel n P M Q tau = true := h
    have hselE : sel = KLie.CT.orN n fun i => 1 <<< (24 * i) := by
      have := Nat.eq_of_beq_eq_true hsel
      rw [this, sel_eq]
    subst hselE
    have hQeq : permRows (mulRows (KLie.CT.orN n fun i => 1 <<< (24 * i)) P M) tau n = Q :=
      Nat.eq_of_beq_eq_true h'
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exact absurd (rowsOK_spec hQ').1 (by
          have : rowOf Q 0 = 0 :=
            rowOf_eq_zero_of_lt (n := 0) (by simp [permRows] at hQeq ⊢; omega) le_rfl
          omega)
      · exact h0
    obtain ⟨hpos, hmono⟩ := rows_pos_mono hQ' hn0
    set Y := mulRows (KLie.CT.orN n fun i => 1 <<< (24 * i)) P M with hYdef
    have hrow : ∀ i < n, rowOf Q i = rowOf Y (tauIdx tau i) := fun i hi => by
      rw [← hQeq, rowOf_permRows _ _ _ hi]
    have hsub : ptS n Q ⊆ actP (ptS n P) y := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
      have hi' := Finset.mem_range.1 hi
      have ht : tauIdx tau i < n := by
        by_contra hge
        have hz : rowOf Y (tauIdx tau i) = 0 :=
          rowOf_eq_zero_of_lt (mulRows_lt n P M) (Nat.le_of_not_lt hge)
        have := hpos i hi'
        rw [hrow i hi', hz] at this
        omega
      refine Finset.mem_image.2 ⟨toVec (rowOf P (tauIdx tau i)),
        Finset.mem_image.2 ⟨_, Finset.mem_range.2 ht, rfl⟩, ?_⟩
      rw [hy, ← toVec_rowOf_mulRows n P M ht, hrow i hi']
    have hinj : Set.InjOn (fun i => toVec (rowOf Q i)) (Finset.range n : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have := eq_of_toVec_eq (rowOf_lt Q i) (rowOf_lt Q j) hij
      rcases lt_trichotomy i j with h1 | h1 | h1
      · exact absurd this (Nat.ne_of_lt (hmono i j h1 hj))
      · exact h1
      · exact absurd this.symm (Nat.ne_of_lt (hmono j i h1 hi))
    have hc1 : (ptS n Q).card = n := by
      unfold ptS
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hc2 : (actP (ptS n P) y).card ≤ n := by
      unfold actP ptS
      refine (Finset.card_image_le).trans ((Finset.card_image_le).trans ?_)
      rw [Finset.card_range]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  · rw [hn] at h
    have hn1 : n = 1 := Nat.eq_of_beq_eq_true hn
    subst hn1
    have hQe : Q = vecmul P M := Nat.eq_of_beq_eq_true h
    have hP' : P < 2 ^ 24 := by simpa using hP
    unfold ptS actP
    simp only [Finset.range_one, Finset.image_singleton]
    rw [rowOf_zero_eq hP', rowOf_zero_eq (hQe ▸ vecmul_lt P M), hQe, hy, toVec_vecmul hP']

theorem ptS_inj {n P Q : ℕ} (hP : P < 2 ^ (24 * n)) (hQ : Q < 2 ^ (24 * n))
    (hPc : n = 1 ∨ rowsOK n P = true) (hQc : n = 1 ∨ rowsOK n Q = true)
    (h : ptS n P = ptS n Q) : P = Q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hP hQ
    rw [hP, hQ]
  by_cases hn1 : n = 1
  · subst hn1
    unfold ptS at h
    simp only [Finset.range_one, Finset.image_singleton, Finset.singleton_inj] at h
    have e := eq_of_toVec_eq (rowOf_lt P 0) (rowOf_lt Q 0) h
    refine eq_of_rows_eq hP hQ fun i hi => ?_
    rw [show i = 0 by omega]
    exact e
  have hPc' := hPc.resolve_left hn1
  have hQc' := hQc.resolve_left hn1
  obtain ⟨-, hmP⟩ := rows_pos_mono hPc' hn0
  obtain ⟨-, hmQ⟩ := rows_pos_mono hQc' hn0
  have hfP : StrictMono (fun i : Fin n => rowOf P i) := fun i j hij => hmP i j hij j.2
  have hfQ : StrictMono (fun i : Fin n => rowOf Q i) := fun i j hij => hmQ i j hij j.2
  have hsub : ∀ {A B : ℕ}, ptS n A = ptS n B → ∀ i : Fin n, ∃ j : Fin n, rowOf B j = rowOf A i := by
    intro A B hAB i
    have hm : toVec (rowOf A i) ∈ ptS n B := by
      rw [← hAB]
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 i.2, rfl⟩
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 hm
    exact ⟨⟨j, Finset.mem_range.1 hj⟩, eq_of_toVec_eq (rowOf_lt B j) (rowOf_lt A i) hjv⟩
  have hr : Set.range (fun i : Fin n => rowOf P i) = Set.range (fun i : Fin n => rowOf Q i) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hsub h i
      exact ⟨j, hj⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hsub h.symm i
      exact ⟨j, hj⟩
  have hf := (hfP.range_inj hfQ).1 hr
  exact eq_of_rows_eq hP hQ fun i hi => congrFun hf ⟨i, hi⟩

theorem permRows_zero (tau n : ℕ) : permRows 0 tau n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_permRows, Nat.zero_testBit]
  simp

theorem actOK_zero {n sel P Q tau : ℕ} (hsel : DceS.selOK n sel = true)
    (hQ : rowsOK n Q = true) (h : DceS.actOK n sel P 0 Q tau = true) : False := by
  have hpos := (rowsOK_spec hQ).1
  unfold DceS.actOK at h
  cases hn : Nat.beq n 1
  · rw [hn] at h
    have h' : chkAct sel n P 0 Q tau = true := h
    have hselE : sel = KLie.CT.orN n fun i => 1 <<< (24 * i) := by
      have := Nat.eq_of_beq_eq_true hsel
      rw [this, sel_eq]
    subst hselE
    have hQeq := Nat.eq_of_beq_eq_true h'
    rw [mulRows_zero_right, permRows_zero] at hQeq
    rw [← hQeq] at hpos
    simp [rowOf] at hpos
  · rw [hn] at h
    have hQe : Q = vecmul P 0 := Nat.eq_of_beq_eq_true h
    have hv0 : vecmul P 0 = 0 := by
      unfold vecmul
      simp [fold1, fold2, fold3, fold45, Nat.and_zero, Nat.zero_xor, Nat.zero_shiftRight]
    rw [hQe, hv0] at hpos
    simp [rowOf] at hpos

end CFSG.KC.Th.Spec.Dce

end
