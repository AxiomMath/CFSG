module

public import CFSG.Certificates.Kernel.McL.Mat25
public import CFSG.Certificates.Kernel.F2WordSound
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.McL.Mat

@[expose] def toMat (A : ℕ) : Matrix (Fin 25) (Fin 25) (ZMod 2) :=
  Matrix.of fun i j => ((A.testBit (25 * (i : ℕ) + j)).toNat : ZMod 2)

@[expose] def toVec (x : ℕ) : Fin 25 → ZMod 2 := fun j => ((x.testBit j).toNat : ZMod 2)

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

theorem rowMask_eq : rowMask = 2 ^ 25 - 1 := rfl

theorem m625_eq : m625 = 2 ^ 625 - 1 := rfl

theorem ident_lt : ident < 2 ^ 625 := by decide +kernel

theorem ident_testBit : ∀ i < 25, ∀ j < 25, ident.testBit (25 * i + j) = decide (i = j) := by
  decide +kernel

theorem testBit_lt_625 {A : ℕ} (hA : A < 2 ^ 625) {p : ℕ} (hp : 625 ≤ p) : A.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hp))

theorem rR_eq : Nat.div (KLie.CT.maskN (Nat.mul 25 25)) (KLie.CT.maskN 25) = c0 := by
  decide +kernel

theorem rF_eq : KLie.CT.maskN 25 = rowMask := by decide +kernel

theorem mul25_eq_mulW (A B : ℕ) : mul25 A B = F2W.mulW 25 A B := by
  rw [F2W.mulW_eq_rec, rR_eq, rF_eq]
  rfl

theorem mul25_eq_mulF (A B : ℕ) : mul25 A B = M1F2.mulF 25 A B := by
  rw [mul25_eq_mulW, F2W.mulW_eq]

theorem mul25_lt (A B : ℕ) : mul25 A B < 2 ^ 625 := by
  rw [mul25_eq_mulF, F2W.mulF_eq_orN]
  exact F2W.orN_fields_lt fun i _ => F2W.vmF_lt 25 B _

theorem testBit_mul25 (A B : ℕ) {i j : ℕ} (hi : i < 25) (hj : j < 25) :
    (mul25 A B).testBit (25 * i + j) =
      Nat.rec (motive := fun _ => Bool) false
        (fun k b => (A.testBit (25 * i + k) && B.testBit (25 * k + j)) ^^ b) 25 := by
  rw [mul25_eq_mulF, F2W.mulF_eq_orN,
    F2W.testBit_orN_fields fun i _ => F2W.vmF_lt 25 B (M1F2.rowF 25 A i)]
  have hq : (25 * i + j) / 25 = i := by omega
  have hr : (25 * i + j) % 25 = j := by omega
  have hd : decide (25 * i + j < 25 * 25) = true := decide_eq_true (by omega)
  rw [hq, hr, hd, Bool.true_and, F2W.testBit_vmF 25 B _ _ hj]
  refine F2W.rec_congr
    (F := fun k b => ((M1F2.rowF 25 A i).testBit k && B.testBit (k * 25 + j)) ^^ b)
    (G := fun k b => (A.testBit (25 * i + k) && B.testBit (25 * k + j)) ^^ b)
    false 25 fun k hk b => ?_
  rw [F2W.testBit_rowF 25 A i k hk, Nat.mul_comm i 25, Nat.mul_comm k 25]

theorem toMat_mul25 (A B : ℕ) : toMat (mul25 A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.mul_apply]
  rw [testBit_mul25 A B i.2 j.2, cast_recXor]
  exact Finset.sum_congr rfl fun k _ => cast_and _ _

@[expose] noncomputable def chain (y : ℕ) : ℕ := sp0 (sp1 (sp2 (sp3 (sp4 y))))

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

theorem chain_or (x y : ℕ) : chain (x ||| y) = chain x ||| chain y := by
  simp only [chain, sp4, sp3, sp2, sp1, sp0, spG_or]

theorem chain_zero : chain 0 = 0 := rfl

theorem chain_pow : ∀ i < 25, chain (1 <<< i) = 1 <<< (25 * i) := by decide +kernel

theorem orN_congr {f g : ℕ → ℕ} : ∀ n : ℕ, (∀ i < n, f i = g i) → KLie.CT.orN n f = KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [F2W.orN_succ, F2W.orN_succ, orN_congr n fun i hi => h i (by omega), h n (by omega)]

theorem chain_orN (f : ℕ → ℕ) : ∀ n : ℕ,
    chain (KLie.CT.orN n f) = KLie.CT.orN n fun i => chain (f i)
  | 0 => chain_zero
  | n + 1 => by rw [F2W.orN_succ, F2W.orN_succ, chain_or, chain_orN f n]

theorem eq_orN_bits {y : ℕ} (hy : y < 2 ^ 25) :
    y = KLie.CT.orN 25 fun i => (y.testBit i).toNat <<< (1 * i) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [F2W.testBit_orN_fields fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega),
    Nat.div_one, Nat.mod_one, Nat.one_mul]
  by_cases hp : p < 25
  · cases y.testBit p <;> simp [hp]
  · simp [hp, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega)
      (Nat.le_of_not_lt hp)))]

theorem chain_eq {y : ℕ} (hy : y < 2 ^ 25) :
    chain y = KLie.CT.orN 25 fun i => (y.testBit i).toNat <<< (25 * i) := by
  conv_lhs => rw [eq_orN_bits hy]
  rw [chain_orN]
  refine orN_congr 25 fun i hi => ?_
  cases y.testBit i
  · simp only [Bool.toNat_false, Nat.zero_shiftLeft]
    exact chain_zero
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact chain_pow i hi

theorem testBit_spreadS {y : ℕ} (hy : y < 2 ^ 25) (r : ℕ) {j : ℕ} (hj : j < 25) :
    (spreadS y).testBit (25 * r + j) = (decide (r < 25) && y.testBit r) := by
  change (Nat.mul (chain y) rowMask).testBit _ = _
  have h1 : ∀ i < 25, (y.testBit i).toNat < 2 ^ 25 :=
    fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega)
  rw [chain_eq hy, rowMask_eq]
  change ((KLie.CT.orN 25 fun i => (y.testBit i).toNat <<< (25 * i)) * (2 ^ 25 - 1)).testBit _ = _
  rw [F2W.orN_fields_mul h1 fun _ _ => F2W.toNat_mul_lt _,
    F2W.testBit_orN_fields fun _ _ => F2W.toNat_mul_lt _]
  have hq : (25 * r + j) / 25 = r := by omega
  have hr : (25 * r + j) % 25 = j := by omega
  rw [hq, hr]
  have hd : decide (25 * r + j < 25 * 25) = decide (r < 25) := by
    by_cases h : r < 25
    · simp [h]; omega
    · simp [h]; omega
  rw [hd]
  cases y.testBit r
  · simp
  · rw [Bool.toNat_true, Nat.one_mul, Nat.testBit_two_pow_sub_one]
    simp [hj]

theorem testBit_fold (s t p : ℕ) : (fold s t).testBit p = (t.testBit p ^^ t.testBit (p + s)) := by
  change (t ^^^ (t >>> s)).testBit p = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.add_comm s p]

theorem testBit_foldR (m t r j : ℕ) :
    (fold (25 * m) t).testBit (25 * r + j) =
      (t.testBit (25 * r + j) ^^ t.testBit (25 * (r + m) + j)) := by
  have h : 25 * r + j + 25 * m = 25 * (r + m) + j := by ring
  rw [testBit_fold, h]

theorem testBit_T (x M r : ℕ) {j : ℕ} (hj : j < 25) :
    (Nat.land (spreadS (Nat.land x rowMask)) M).testBit (25 * r + j) =
      (decide (r < 25) && (x.testBit r && M.testBit (25 * r + j))) := by
  have hy : x &&& rowMask < 2 ^ 25 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by rw [rowMask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
  change (spreadS (x &&& rowMask) &&& M).testBit _ = _
  rw [Nat.testBit_and, testBit_spreadS hy r hj]
  rw [Nat.testBit_and, rowMask_eq, Nat.testBit_two_pow_sub_one]
  by_cases h : r < 25 <;> simp [h]

theorem rowMask_testBit {j : ℕ} (hj : j < 25) : rowMask.testBit j = true := by
  rw [rowMask_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem vecmul_lt (x M : ℕ) : vecmul x M < 2 ^ 25 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by rw [rowMask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem cast_testBit_vecmul (x M : ℕ) {j : ℕ} (hj : j < 25) :
    (((vecmul x M).testBit j).toNat : ZMod 2) =
      ∑ k : Fin 25, ((x.testBit k).toNat : ZMod 2) * (M.testBit (25 * k + j)).toNat := by
  change ((((fold (25 * 1) (fold (25 * 2) (fold (25 * 4) (fold (25 * 8) (fold (25 * 16)
    (Nat.land (spreadS (Nat.land x rowMask)) M))))) &&& rowMask).testBit j).toNat : ℕ) : ZMod 2) = _
  have h0 : j = 25 * 0 + j := by omega
  rw [Nat.testBit_and, rowMask_testBit hj, Bool.and_true]
  conv_lhs => rw [h0]
  simp only [testBit_foldR, testBit_T x M _ hj, cast_xor, cast_and, Nat.reduceAdd, -Nat.reduceMul,
    Nat.reduceLT, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.toNat_false,
    Nat.cast_zero, add_zero, zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((x.testBit k).toNat : ZMod 2) *
    (M.testBit (25 * k + j)).toNat) 25]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem toVec_vecmul (x M : ℕ) : toVec (vecmul x M) = Matrix.vecMul (toVec x) (toMat M) := by
  funext j
  simp only [toVec, toMat, Matrix.vecMul, dotProduct, Matrix.of_apply]
  exact cast_testBit_vecmul x M j.2

theorem toMat_ident : toMat ident = 1 := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.one_apply]
  rw [ident_testBit i i.2 j j.2]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Fin.val_inj]

theorem land_m625_lt (y : ℕ) : Nat.land y m625 < 2 ^ 625 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by rw [m625_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem land_rowMask_lt (y : ℕ) : Nat.land y rowMask < 2 ^ 25 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by rw [rowMask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)

theorem toMat_land_m625 (y : ℕ) : toMat (Nat.land y m625) = toMat y := by
  ext i j
  simp only [toMat, Matrix.of_apply]
  change (((y &&& m625).testBit _).toNat : ZMod 2) = _
  have hd : decide (25 * (i : ℕ) + j < 625) = true := decide_eq_true (by omega)
  rw [Nat.testBit_and, m625_eq, Nat.testBit_two_pow_sub_one, hd, Bool.and_true]

theorem toVec_land_rowMask (y : ℕ) : toVec (Nat.land y rowMask) = toVec y := by
  funext j
  simp only [toVec]
  change (((y &&& rowMask).testBit _).toNat : ZMod 2) = _
  have hd : decide ((j : ℕ) < 25) = true := decide_eq_true j.2
  rw [Nat.testBit_and, rowMask_eq, Nat.testBit_two_pow_sub_one, hd, Bool.and_true]

theorem eq_of_toMat_eq {A B : ℕ} (hA : A < 2 ^ 625) (hB : B < 2 ^ 625) (h : toMat A = toMat B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 625
  · have h' := congrFun (congrFun h ⟨p / 25, by omega⟩) ⟨p % 25, Nat.mod_lt _ (by omega)⟩
    simp only [toMat, Matrix.of_apply, Nat.div_add_mod] at h'
    exact eq_of_cast_eq h'
  · rw [testBit_lt_625 hA (by omega), testBit_lt_625 hB (by omega)]

theorem eq_of_toVec_eq {x y : ℕ} (hx : x < 2 ^ 25) (hy : y < 2 ^ 25) (h : toVec x = toVec y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 25
  · exact eq_of_cast_eq (congrFun h ⟨p, hp⟩)
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem mul25_assoc (A B C : ℕ) : mul25 (mul25 A B) C = mul25 A (mul25 B C) :=
  eq_of_toMat_eq (mul25_lt _ _) (mul25_lt _ _) (by simp only [toMat_mul25, Matrix.mul_assoc])

theorem ident_mul25 {A : ℕ} (hA : A < 2 ^ 625) : mul25 ident A = A :=
  eq_of_toMat_eq (mul25_lt _ _) hA (by rw [toMat_mul25, toMat_ident, Matrix.one_mul])

theorem mul25_ident {A : ℕ} (hA : A < 2 ^ 625) : mul25 A ident = A :=
  eq_of_toMat_eq (mul25_lt _ _) hA (by rw [toMat_mul25, toMat_ident, Matrix.mul_one])

theorem vecmul_mul25 (x A B : ℕ) : vecmul (vecmul x A) B = vecmul x (mul25 A B) :=
  eq_of_toVec_eq (vecmul_lt _ _) (vecmul_lt _ _)
    (by rw [toVec_vecmul, toVec_vecmul, toVec_vecmul, toMat_mul25, Matrix.vecMul_vecMul])

theorem vecmul_ident {x : ℕ} (hx : x < 2 ^ 25) : vecmul x ident = x :=
  eq_of_toVec_eq (vecmul_lt _ _) hx (by rw [toVec_vecmul, toMat_ident, Matrix.vecMul_one])

end CFSG.KC.McL.Mat

end
