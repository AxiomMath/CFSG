module

public import CFSG.Certificates.Kernel.J4.DceS
public import CFSG.Certificates.Kernel.F2WordSound
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KJ4.Mat

open CFSG.KJ4 CFSG.KC
open scoped Matrix

@[expose] def toMat (A : ℕ) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  Matrix.of fun i j => ((A.testBit (12 * (i : ℕ) + j)).toNat : ZMod 2)

@[expose] def toVec (x : ℕ) : Fin 12 → ZMod 2 := fun j => ((x.testBit j).toNat : ZMod 2)

theorem toMat_apply (A : ℕ) (i j : Fin 12) :
    toMat A i j = ((A.testBit (12 * (i : ℕ) + j)).toNat : ZMod 2) := rfl

theorem cast_xor (a b : Bool) : (((a ^^ b).toNat : ℕ) : ZMod 2) = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide

theorem cast_and (a b : Bool) : (((a && b).toNat : ℕ) : ZMod 2) = a.toNat * b.toNat := by
  cases a <;> cases b <;> decide

theorem eq_of_cast_eq {a b : Bool} (h : ((a.toNat : ℕ) : ZMod 2) = b.toNat) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem cast_eq_zero_iff (a : Bool) : ((a.toNat : ℕ) : ZMod 2) = 0 ↔ a = false := by
  cases a <;> decide

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

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem beq_eq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

set_option exponentiation.threshold 300

theorem rowMask_eq : rowMask = 2 ^ 12 - 1 := rfl

theorem ident12_lt : ident12 < 2 ^ 144 := by decide +kernel

theorem ident12_testBit : ∀ i < 12, ∀ j < 12, ident12.testBit (12 * i + j) = decide (i = j) := by
  decide +kernel

theorem colMask_lt : colMask < 2 ^ 144 := by decide +kernel

theorem linMask_lt : linMask < 2 ^ 144 := by decide +kernel

theorem testBit_lt_144 {A : ℕ} (hA : A < 2 ^ 144) {p : ℕ} (hp : 144 ≤ p) : A.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hp))

theorem testBit_lt_12 {x : ℕ} (hx : x < 2 ^ 12) {p : ℕ} (hp : 12 ≤ p) : x.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hp))

theorem rowMask_testBit {j : ℕ} (hj : j < 12) : rowMask.testBit j = true := by
  rw [rowMask_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem land_rowMask_lt (y : ℕ) : Nat.land y rowMask < 2 ^ 12 :=
  Nat.and_lt_two_pow _ (by decide)

theorem rR_eq : Nat.div (KLie.CT.maskN (Nat.mul 12 12)) (KLie.CT.maskN 12) = c0 := by
  decide +kernel

theorem rF_eq : KLie.CT.maskN 12 = rowMask := by decide +kernel

theorem mul12_eq_mulW (A B : ℕ) : mul12 A B = F2W.mulW 12 A B := by
  rw [F2W.mulW_eq_rec, rR_eq, rF_eq]
  rfl

theorem mul12_eq_mulF (A B : ℕ) : mul12 A B = M1F2.mulF 12 A B := by
  rw [mul12_eq_mulW, F2W.mulW_eq]

theorem mul12_lt (A B : ℕ) : mul12 A B < 2 ^ 144 := by
  rw [mul12_eq_mulF, F2W.mulF_eq_orN]
  exact F2W.orN_fields_lt fun i _ => F2W.vmF_lt 12 B _

theorem testBit_mul12 (A B : ℕ) {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    (mul12 A B).testBit (12 * i + j) =
      Nat.rec (motive := fun _ => Bool) false
        (fun k b => (A.testBit (12 * i + k) && B.testBit (12 * k + j)) ^^ b) 12 := by
  rw [mul12_eq_mulF, F2W.mulF_eq_orN,
    F2W.testBit_orN_fields fun i _ => F2W.vmF_lt 12 B (M1F2.rowF 12 A i)]
  have hq : (12 * i + j) / 12 = i := by omega
  have hr : (12 * i + j) % 12 = j := by omega
  have hd : decide (12 * i + j < 12 * 12) = true := decide_eq_true (by omega)
  rw [hq, hr, hd, Bool.true_and, F2W.testBit_vmF 12 B _ _ hj]
  refine F2W.rec_congr
    (F := fun k b => ((M1F2.rowF 12 A i).testBit k && B.testBit (k * 12 + j)) ^^ b)
    (G := fun k b => (A.testBit (12 * i + k) && B.testBit (12 * k + j)) ^^ b)
    false 12 fun k hk b => ?_
  rw [F2W.testBit_rowF 12 A i k hk, Nat.mul_comm i 12, Nat.mul_comm k 12]

theorem toMat_mul12 (A B : ℕ) : toMat (mul12 A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.mul_apply]
  rw [testBit_mul12 A B i.2 j.2, cast_recXor]
  exact Finset.sum_congr rfl fun k _ => cast_and _ _

@[expose] noncomputable def chain (y : ℕ) : ℕ := sp3 (sp2 (sp1 y))

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

theorem sp3_or (x y : ℕ) : sp3 (x ||| y) = sp3 x ||| sp3 y := by
  change ((x ||| y) &&& m3a ||| ((x ||| y) &&& m3b) <<< 11) ||| ((x ||| y) &&& m3c) <<< 22 =
    ((x &&& m3a ||| (x &&& m3b) <<< 11) ||| (x &&& m3c) <<< 22) |||
      ((y &&& m3a ||| (y &&& m3b) <<< 11) ||| (y &&& m3c) <<< 22)
  rw [Nat.and_or_distrib_right, Nat.and_or_distrib_right, Nat.and_or_distrib_right,
    Nat.shiftLeft_or_distrib, Nat.shiftLeft_or_distrib]
  generalize x &&& m3a = a1
  generalize y &&& m3a = a2
  generalize (x &&& m3b) <<< 11 = b1
  generalize (y &&& m3b) <<< 11 = b2
  generalize (x &&& m3c) <<< 22 = c1
  generalize (y &&& m3c) <<< 22 = c2
  ac_rfl

theorem sp1_or (x y : ℕ) : sp1 (x ||| y) = sp1 x ||| sp1 y := spG_or _ _ _ x y

theorem sp2_or (x y : ℕ) : sp2 (x ||| y) = sp2 x ||| sp2 y := spG_or _ _ _ x y

theorem chain_or (x y : ℕ) : chain (x ||| y) = chain x ||| chain y := by
  rw [chain, chain, chain, sp1_or, sp2_or, sp3_or]

theorem chain_zero : chain 0 = 0 := by decide +kernel

theorem chain_pow : ∀ i < 12, chain (1 <<< i) = 1 <<< (12 * i) := by decide +kernel

theorem orN_congr {f g : ℕ → ℕ} : ∀ n : ℕ, (∀ i < n, f i = g i) → KLie.CT.orN n f = KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [F2W.orN_succ, F2W.orN_succ, orN_congr n fun i hi => h i (by omega), h n (by omega)]

theorem chain_orN (f : ℕ → ℕ) : ∀ n : ℕ,
    chain (KLie.CT.orN n f) = KLie.CT.orN n fun i => chain (f i)
  | 0 => chain_zero
  | n + 1 => by rw [F2W.orN_succ, F2W.orN_succ, chain_or, chain_orN f n]

theorem eq_orN_bits {y : ℕ} (hy : y < 2 ^ 12) :
    y = KLie.CT.orN 12 fun i => (y.testBit i).toNat <<< (1 * i) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [F2W.testBit_orN_fields fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega),
    Nat.div_one, Nat.mod_one, Nat.one_mul]
  by_cases hp : p < 12
  · cases y.testBit p <;> simp [hp]
  · simp [hp, testBit_lt_12 hy (Nat.le_of_not_lt hp)]

theorem chain_eq {y : ℕ} (hy : y < 2 ^ 12) :
    chain y = KLie.CT.orN 12 fun i => (y.testBit i).toNat <<< (12 * i) := by
  conv_lhs => rw [eq_orN_bits hy]
  rw [chain_orN]
  refine orN_congr 12 fun i hi => ?_
  cases y.testBit i
  · simp only [Bool.toNat_false, Nat.zero_shiftLeft]
    exact chain_zero
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact chain_pow i hi

theorem sp1_land (x : ℕ) : sp1 x = sp1 (Nat.land x rowMask) := by
  change Nat.lor (Nat.land x 63) (Nat.shiftLeft (Nat.land x 4032) 66) =
    Nat.lor (Nat.land (x &&& rowMask) 63) (Nat.shiftLeft (Nat.land (x &&& rowMask) 4032) 66)
  change Nat.lor (x &&& 63) (Nat.shiftLeft (x &&& 4032) 66) =
    Nat.lor ((x &&& rowMask) &&& 63) (Nat.shiftLeft ((x &&& rowMask) &&& 4032) 66)
  rw [Nat.and_assoc, Nat.and_assoc]
  rfl

theorem testBit_spreadS (x r : ℕ) {j : ℕ} (hj : j < 12) :
    (spreadS x).testBit (12 * r + j) = (decide (r < 12) && x.testBit r) := by
  have hy : Nat.land x rowMask < 2 ^ 12 := land_rowMask_lt x
  change (Nat.mul (chain x) rowMask).testBit _ = _
  have hc : chain x = chain (Nat.land x rowMask) := by rw [chain, chain, sp1_land]
  have h1 : ∀ i < 12, ((Nat.land x rowMask).testBit i).toNat < 2 ^ 12 :=
    fun i _ => Nat.lt_of_le_of_lt (Bool.toNat_le _) (by omega)
  rw [hc, chain_eq hy, rowMask_eq]
  change ((KLie.CT.orN 12 fun i => ((Nat.land x rowMask).testBit i).toNat <<< (12 * i)) *
    (2 ^ 12 - 1)).testBit _ = _
  rw [F2W.orN_fields_mul h1 fun _ _ => F2W.toNat_mul_lt _,
    F2W.testBit_orN_fields fun _ _ => F2W.toNat_mul_lt _]
  have hq : (12 * r + j) / 12 = r := by omega
  have hr : (12 * r + j) % 12 = j := by omega
  rw [hq, hr]
  have hd : decide (12 * r + j < 12 * 12) = decide (r < 12) := by
    by_cases h : r < 12
    · simp [h]; omega
    · simp [h]; omega
  rw [hd]
  by_cases hr12 : r < 12
  · have hb : (Nat.land x rowMask).testBit r = x.testBit r := by
      change (x &&& rowMask).testBit r = _
      rw [Nat.testBit_and, rowMask_testBit hr12, Bool.and_true]
    rw [hb]
    cases x.testBit r
    · simp
    · rw [Bool.toNat_true, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simp [hj, hr12]
  · simp [hr12]

theorem testBit_fold1 (t r j : ℕ) :
    (fold1 t).testBit (12 * r + j) = (t.testBit (12 * r + j) ^^ t.testBit (12 * (r + 6) + j)) := by
  change (t ^^^ (t >>> 72)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  congr 2
  ring

theorem testBit_fold2 (t r j : ℕ) :
    (fold2 t).testBit (12 * r + j) = (t.testBit (12 * r + j) ^^ t.testBit (12 * (r + 3) + j)) := by
  change (t ^^^ (t >>> 36)).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_shiftRight]
  congr 2
  ring

theorem testBit_fold3 (t r j : ℕ) :
    (fold3 t).testBit (12 * r + j) = (t.testBit (12 * r + j) ^^
      (t.testBit (12 * (r + 1) + j) ^^ t.testBit (12 * (r + 2) + j))) := by
  change (t ^^^ ((t >>> 12) ^^^ (t >>> 24))).testBit _ = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  congr 3 <;> ring

theorem testBit_T (x M r : ℕ) {j : ℕ} (hj : j < 12) :
    (Nat.land (spreadS x) M).testBit (12 * r + j) =
      (decide (r < 12) && (x.testBit r && M.testBit (12 * r + j))) := by
  change (spreadS x &&& M).testBit _ = _
  rw [Nat.testBit_and, testBit_spreadS x r hj]
  by_cases h : r < 12 <;> simp [h]

theorem vecmul_lt (x M : ℕ) : vecmul x M < 2 ^ 12 := land_rowMask_lt _

theorem cast_testBit_vecmul (x M : ℕ) {j : ℕ} (hj : j < 12) :
    (((vecmul x M).testBit j).toNat : ZMod 2) =
      ∑ k : Fin 12, ((x.testBit k).toNat : ZMod 2) * (M.testBit (12 * k + j)).toNat := by
  change ((((fold3 (fold2 (fold1 (Nat.land (spreadS x) M))) &&& rowMask).testBit j).toNat : ℕ) :
    ZMod 2) = _
  have h0 : j = 12 * 0 + j := by omega
  rw [Nat.testBit_and, rowMask_testBit hj, Bool.and_true]
  conv_lhs => rw [h0]
  simp only [testBit_fold3, testBit_fold2, testBit_fold1, testBit_T x M _ hj, cast_xor, cast_and,
    Nat.reduceAdd, -Nat.reduceMul, Nat.reduceLT, decide_true, Bool.true_and]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((x.testBit k).toNat : ZMod 2) *
    (M.testBit (12 * k + j)).toNat) 12]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem toVec_vecmul (x M : ℕ) : toVec (vecmul x M) = toVec x ᵥ* toMat M := by
  funext j
  simp only [toVec, toMat, Matrix.vecMul, dotProduct, Matrix.of_apply]
  exact cast_testBit_vecmul x M j.2

theorem toMat_ident12 : toMat ident12 = 1 := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.one_apply]
  rw [ident12_testBit i i.2 j j.2]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Fin.val_inj]

theorem eq_of_toMat_eq {A B : ℕ} (hA : A < 2 ^ 144) (hB : B < 2 ^ 144) (h : toMat A = toMat B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 144
  · have h' := congrFun (congrFun h ⟨p / 12, by omega⟩) ⟨p % 12, Nat.mod_lt _ (by omega)⟩
    simp only [toMat, Matrix.of_apply, Nat.div_add_mod] at h'
    exact eq_of_cast_eq h'
  · rw [testBit_lt_144 hA (by omega), testBit_lt_144 hB (by omega)]

theorem toMat_inj {A B : ℕ} (hA : A < 2 ^ 144) (hB : B < 2 ^ 144) : toMat A = toMat B ↔ A = B :=
  ⟨eq_of_toMat_eq hA hB, fun h => h ▸ rfl⟩

theorem eq_of_toVec_eq {x y : ℕ} (hx : x < 2 ^ 12) (hy : y < 2 ^ 12) (h : toVec x = toVec y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 12
  · exact eq_of_cast_eq (congrFun h ⟨p, hp⟩)
  · rw [testBit_lt_12 hx (by omega), testBit_lt_12 hy (by omega)]

theorem toVec_inj {x y : ℕ} (hx : x < 2 ^ 12) (hy : y < 2 ^ 12) : toVec x = toVec y ↔ x = y :=
  ⟨eq_of_toVec_eq hx hy, fun h => h ▸ rfl⟩

theorem toMat_zero : toMat 0 = 0 := by
  ext i j
  simp [toMat]

theorem toVec_zero : toVec 0 = 0 := by
  funext j
  simp [toVec]

theorem toVec_eq_zero_iff {x : ℕ} (hx : x < 2 ^ 12) : toVec x = 0 ↔ x = 0 := by
  rw [← toVec_zero]
  exact toVec_inj hx (Nat.two_pow_pos 12)

theorem toVec_xor (a b : ℕ) : toVec (a ^^^ b) = toVec a + toVec b := by
  funext j
  simp only [toVec, Pi.add_apply, Nat.testBit_xor, cast_xor]

theorem toMat_land (A K : ℕ) (i j : Fin 12) : toMat (A &&& K) i j = toMat A i j * toMat K i j := by
  simp only [toMat, Matrix.of_apply, Nat.testBit_and, cast_and]

theorem mul12_assoc (A B C : ℕ) : mul12 (mul12 A B) C = mul12 A (mul12 B C) :=
  eq_of_toMat_eq (mul12_lt _ _) (mul12_lt _ _) (by simp only [toMat_mul12, Matrix.mul_assoc])

theorem ident12_mul12 {A : ℕ} (hA : A < 2 ^ 144) : mul12 ident12 A = A :=
  eq_of_toMat_eq (mul12_lt _ _) hA (by rw [toMat_mul12, toMat_ident12, Matrix.one_mul])

theorem mul12_ident12 {A : ℕ} (hA : A < 2 ^ 144) : mul12 A ident12 = A :=
  eq_of_toMat_eq (mul12_lt _ _) hA (by rw [toMat_mul12, toMat_ident12, Matrix.mul_one])

theorem vecmul_mul12 (x A B : ℕ) : vecmul (vecmul x A) B = vecmul x (mul12 A B) :=
  eq_of_toVec_eq (vecmul_lt _ _) (vecmul_lt _ _)
    (by rw [toVec_vecmul, toVec_vecmul, toVec_vecmul, toMat_mul12, Matrix.vecMul_vecMul])

theorem vecmul_ident12 {x : ℕ} (hx : x < 2 ^ 12) : vecmul x ident12 = x :=
  eq_of_toVec_eq (vecmul_lt _ _) hx (by rw [toVec_vecmul, toMat_ident12, Matrix.vecMul_one])

theorem vecmul_xor (a b M : ℕ) : vecmul (a ^^^ b) M = vecmul a M ^^^ vecmul b M :=
  eq_of_toVec_eq (vecmul_lt _ _) (Nat.xor_lt_two_pow (vecmul_lt _ _) (vecmul_lt _ _))
    (by rw [toVec_vecmul, toVec_xor, toVec_xor, toVec_vecmul, toVec_vecmul, Matrix.add_vecMul])

theorem mulF_eq (A B : ℕ) : S.mulF A B = mul12 A B := by
  simp only [S.mulF, F2W.strictN_eq]

theorem chkMul_iff {C A B : ℕ} : chkMul C A B = true ↔ C = mul12 A B := beq_eq_true

theorem chkMul_sound {C A B : ℕ} (h : chkMul C A B = true) : toMat C = toMat A * toMat B := by
  rw [chkMul_iff.1 h, toMat_mul12]

theorem chkInv_sound {A B : ℕ} (h : chkInv A B = true) : toMat A * toMat B = 1 := by
  rw [← toMat_mul12, beq_eq_true.1 h, toMat_ident12]

theorem chkInv_sound' {A B : ℕ} (h : chkInv A B = true) : toMat B * toMat A = 1 :=
  mul_eq_one_comm.1 (chkInv_sound h)

theorem colMask_testBit : ∀ i < 12, ∀ j < 12,
    colMask.testBit (12 * i + j) = (decide (j = 11) && !decide (i = 11)) := by
  decide +kernel

theorem linMask_testBit : ∀ i < 12, ∀ j < 12,
    linMask.testBit (12 * i + j) = !(decide (j = 11) && !decide (i = 11)) := by
  decide +kernel

theorem val_eq_eleven {i : Fin 12} : (i : ℕ) = 11 ↔ i = 11 := ⟨fun h => Fin.ext h, fun h => h ▸ rfl⟩

theorem toMat_colMask (i j : Fin 12) : toMat colMask i j = if j = 11 ∧ i ≠ 11 then 1 else 0 := by
  rw [toMat_apply, colMask_testBit i i.2 j j.2]
  by_cases hj : j = 11 <;> by_cases hi : i = 11 <;> simp [hj, hi, val_eq_eleven]

theorem toMat_linMask (i j : Fin 12) : toMat linMask i j = if j = 11 ∧ i ≠ 11 then 0 else 1 := by
  rw [toMat_apply, linMask_testBit i i.2 j j.2]
  by_cases hj : j = 11 <;> by_cases hi : i = 11 <;> simp [hj, hi, val_eq_eleven]

theorem toMat_land_colMask (A : ℕ) (i j : Fin 12) :
    toMat (A &&& colMask) i j = if j = 11 ∧ i ≠ 11 then toMat A i j else 0 := by
  rw [toMat_land, toMat_colMask]
  split_ifs <;> simp

theorem toMat_land_linMask (A : ℕ) (i j : Fin 12) :
    toMat (A &&& linMask) i j = if j = 11 ∧ i ≠ 11 then 0 else toMat A i j := by
  rw [toMat_land, toMat_linMask]
  split_ifs <;> simp

theorem land_linMask_lt (A : ℕ) : A &&& linMask < 2 ^ 144 := Nat.and_lt_two_pow _ linMask_lt

theorem land_colMask_lt (A : ℕ) : A &&& colMask < 2 ^ 144 := Nat.and_lt_two_pow _ colMask_lt

theorem chkLin_iff {A : ℕ} : chkLin A = true ↔ ∀ i : Fin 12, i ≠ 11 → toMat A i 11 = 0 := by
  change Nat.beq (A &&& colMask) 0 = true ↔ _
  rw [beq_eq_true, ← toMat_inj (land_colMask_lt A) (Nat.two_pow_pos 144), toMat_zero]
  constructor
  · intro h i hi
    have := congrFun (congrFun h i) 11
    rwa [toMat_land_colMask, ite_eq_left ⟨rfl, hi⟩] at this
  · intro h
    ext i j
    rw [toMat_land_colMask]
    split_ifs with hij
    · rw [hij.1]
      exact h i hij.2
    · rfl

theorem chkTrans_iff {A : ℕ} : chkTrans A = true ↔
    ∀ i j : Fin 12, ¬ (j = 11 ∧ i ≠ 11) → toMat A i j = (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) i j := by
  change Nat.beq (A &&& linMask) ident12 = true ↔ _
  rw [beq_eq_true, ← toMat_inj (land_linMask_lt A) ident12_lt, toMat_ident12]
  constructor
  · intro h i j hij
    have := congrFun (congrFun h i) j
    rwa [toMat_land_linMask, ite_eq_right hij] at this
  · intro h
    ext i j
    rw [toMat_land_linMask]
    split_ifs with hij
    · rw [Matrix.one_apply_ne]
      intro e
      exact hij.2 (e.trans hij.1)
    · exact h i j hij

theorem row11_iff {M : ℕ} : Nat.beq (Nat.land (Nat.shiftRight M 132) 4095) 2048 = true ↔
    ∀ j : Fin 12, toMat M 11 j = if j = 11 then 1 else 0 := by
  have hlt : Nat.land (Nat.shiftRight M 132) 4095 < 2 ^ 12 := land_rowMask_lt _
  have h1 : ∀ j : Fin 12, toVec (Nat.land (Nat.shiftRight M 132) 4095) j = toMat M 11 j := by
    intro j
    change ((((M >>> 132) &&& rowMask).testBit j).toNat : ZMod 2) = _
    rw [Nat.testBit_and, rowMask_testBit j.2, Bool.and_true, Nat.testBit_shiftRight, toMat_apply]
    rfl
  have hb : ∀ j < 12, (2048 : ℕ).testBit j = decide (j = 11) := by decide
  have h2 : ∀ j : Fin 12, toVec 2048 j = if j = 11 then 1 else 0 := by
    intro j
    change (((2048 : ℕ).testBit j).toNat : ZMod 2) = _
    rw [hb j j.2]
    by_cases hj : j = 11 <;> simp [hj, val_eq_eleven]
  rw [beq_eq_true]
  constructor
  · intro h j
    rw [← h1, h, h2]
  · intro h
    exact eq_of_toVec_eq hlt (by decide) (funext fun j => by rw [h1, h, h2])

theorem pv_lt (P i : ℕ) : pv P i < 2 ^ 12 := land_rowMask_lt _

theorem testBit_pv (P i : ℕ) {j : ℕ} (hj : j < 12) : (pv P i).testBit j = P.testBit (12 * i + j) := by
  change ((P >>> (12 * i)) &&& rowMask).testBit j = _
  rw [Nat.testBit_and, rowMask_testBit hj, Bool.and_true, Nat.testBit_shiftRight, Nat.add_comm]

theorem ptOK_spec {P : ℕ} (h : ptOK P = true) :
    0 < pv P 0 ∧ pv P 0 < pv P 1 ∧ pv P 1 < pv P 2 ∧ P < 2 ^ 36 ∧ pv P 0 ^^^ pv P 1 = pv P 2 := by
  simp only [ptOK, andB_eq_true, blt_eq_true, beq_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem eq_of_pv {P Q : ℕ} (hP : P < 2 ^ 36) (hQ : Q < 2 ^ 36) (h : ∀ i < 3, pv P i = pv Q i) :
    P = Q := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 36
  · have e : p = 12 * (p / 12) + p % 12 := (Nat.div_add_mod p 12).symm
    have hm : p % 12 < 12 := Nat.mod_lt _ (by omega)
    rw [e, ← testBit_pv P _ hm, ← testBit_pv Q _ hm, h _ (by omega)]
  · have h36 : 2 ^ 36 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hP h36),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hQ h36)]

@[expose] noncomputable def ptVecs (P : ℕ) : Set (Fin 12 → ZMod 2) :=
  {toVec (pv P 0), toVec (pv P 1), toVec (pv P 2)}

@[expose] noncomputable def ptSub (P : ℕ) : Submodule (ZMod 2) (Fin 12 → ZMod 2) :=
  Submodule.span (ZMod 2) (ptVecs P)

theorem mem_ptSub {P : ℕ} (hP : ptOK P = true) {v : Fin 12 → ZMod 2} :
    v ∈ ptSub P ↔ v = 0 ∨ v ∈ ptVecs P := by
  obtain ⟨-, -, -, -, h2⟩ := ptOK_spec hP
  have e2 : toVec (pv P 2) = toVec (pv P 0) + toVec (pv P 1) := by rw [← h2, toVec_xor]
  simp only [ptSub, ptVecs, Submodule.mem_span_triple, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, c, rfl⟩
    rw [e2]
    generalize toVec (pv P 0) = x
    generalize toVec (pv P 1) = y
    have hv : a • x + b • y + c • (x + y) = (a + c) • x + (b + c) • y := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hv]
    generalize a + c = s
    generalize b + c = t
    have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
    rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, 0, by simp⟩
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩

theorem zero_not_mem_ptVecs {P : ℕ} (hP : ptOK P = true) : (0 : Fin 12 → ZMod 2) ∉ ptVecs P := by
  obtain ⟨h0, h01, h12, -, -⟩ := ptOK_spec hP
  simp only [ptVecs, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h | h) <;> rw [eq_comm, toVec_eq_zero_iff (pv_lt _ _)] at h <;> omega

theorem ptVecs_eq_of_ptSub_eq {P Q : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (h : ptSub P = ptSub Q) : ptVecs P = ptVecs Q := by
  ext v
  have hv := (mem_ptSub hP (v := v)).symm.trans ((SetLike.ext_iff.1 h v).trans (mem_ptSub hQ))
  constructor
  · intro hm
    rcases hv.1 (Or.inr hm) with rfl | h'
    · exact absurd hm (zero_not_mem_ptVecs hP)
    · exact h'
  · intro hm
    rcases hv.2 (Or.inr hm) with rfl | h'
    · exact absurd hm (zero_not_mem_ptVecs hQ)
    · exact h'

theorem eq_of_ptVecs_eq {P Q : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (h : ptVecs P = ptVecs Q) : P = Q := by
  obtain ⟨-, a01, a12, aP, -⟩ := ptOK_spec hP
  obtain ⟨-, b01, b12, bQ, -⟩ := ptOK_spec hQ
  have mem : ∀ {P Q : ℕ}, ptVecs P = ptVecs Q → ∀ i < 3,
      pv P i = pv Q 0 ∨ pv P i = pv Q 1 ∨ pv P i = pv Q 2 := by
    intro P Q h i hi
    have hm : toVec (pv P i) ∈ ptVecs Q := by
      rw [← h]
      simp only [ptVecs, Set.mem_insert_iff, Set.mem_singleton_iff]
      interval_cases i <;> simp
    simp only [ptVecs, Set.mem_insert_iff, Set.mem_singleton_iff,
      toVec_inj (pv_lt _ _) (pv_lt _ _)] at hm
    exact hm
  have p0 := mem h 0 (by omega)
  have p1 := mem h 1 (by omega)
  have p2 := mem h 2 (by omega)
  have q0 := mem h.symm 0 (by omega)
  have q1 := mem h.symm 1 (by omega)
  have q2 := mem h.symm 2 (by omega)
  refine eq_of_pv aP bQ fun i hi => ?_
  interval_cases i <;> omega

theorem eq_of_ptSub_eq {P Q : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (h : ptSub P = ptSub Q) : P = Q :=
  eq_of_ptVecs_eq hP hQ (ptVecs_eq_of_ptSub_eq hP hQ h)

theorem sel_cases : ∀ h < 6,
    (sel h 0 = 0 ∧ sel h 1 = 1 ∧ sel h 2 = 2) ∨ (sel h 0 = 0 ∧ sel h 1 = 2 ∧ sel h 2 = 1) ∨
    (sel h 0 = 1 ∧ sel h 1 = 0 ∧ sel h 2 = 2) ∨ (sel h 0 = 1 ∧ sel h 1 = 2 ∧ sel h 2 = 0) ∨
    (sel h 0 = 2 ∧ sel h 1 = 0 ∧ sel h 2 = 1) ∨ (sel h 0 = 2 ∧ sel h 1 = 1 ∧ sel h 2 = 0) := by
  decide +kernel

theorem xor_of_xor {a b c : ℕ} (h : a ^^^ b = c) :
    b ^^^ a = c ∧ a ^^^ c = b ∧ c ^^^ a = b ∧ b ^^^ c = a ∧ c ^^^ b = a := by
  subst h
  refine ⟨Nat.xor_comm _ _, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rw [Nat.xor_comm a b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · rw [Nat.xor_comm, Nat.xor_comm a b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem chkPt_vec {P g Q h : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (hc : chkPt P g Q h = true) : h < 6 ∧ ∀ i < 3, vecmul (pv P i) g = pv Q (sel h i) := by
  simp only [chkPt, andB_eq_true, blt_eq_true, beq_eq_true] at hc
  obtain ⟨h6, e0, e1⟩ := hc
  obtain ⟨-, -, -, -, hp⟩ := ptOK_spec hP
  obtain ⟨-, -, -, -, hq⟩ := ptOK_spec hQ
  have e2 : vecmul (pv P 2) g = pv Q (sel h 0) ^^^ pv Q (sel h 1) := by
    rw [← hp, vecmul_xor, e0, e1]
  refine ⟨h6, fun i hi => ?_⟩
  interval_cases i
  · exact e0
  · exact e1
  · rw [e2]
    have x := xor_of_xor hq
    rcases sel_cases h h6 with ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ |
      ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ <;> rw [s0, s1, s2] <;> first | exact hq | tauto

theorem chkPt_image {P g Q h : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (hc : chkPt P g Q h = true) : (fun v => v ᵥ* toMat g) '' ptVecs P = ptVecs Q := by
  obtain ⟨h6, e⟩ := chkPt_vec hP hQ hc
  have hv : ∀ i < 3, toVec (pv P i) ᵥ* toMat g = toVec (pv Q (sel h i)) := fun i hi => by
    rw [← toVec_vecmul, e i hi]
  simp only [ptVecs, Set.image_insert_eq, Set.image_singleton, hv 0 (by omega), hv 1 (by omega),
    hv 2 (by omega)]
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases sel_cases h h6 with ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ |
    ⟨s0, s1, s2⟩ | ⟨s0, s1, s2⟩ <;> rw [s0, s1, s2] <;> tauto

theorem chkPt_map {P g Q h : ℕ} (hP : ptOK P = true) (hQ : ptOK Q = true)
    (hc : chkPt P g Q h = true) : (ptSub P).map (toMat g).vecMulLinear = ptSub Q := by
  rw [ptSub, Submodule.map_span, ptSub, ← chkPt_image hP hQ hc]
  rfl

theorem chkPtF_eq (P g Q h : ℕ) : S.chkPtF P g Q h = chkPt P g Q h := by
  cases P <;> cases g <;> cases Q <;> rfl

theorem image_vecMul_mul (A B : Matrix (Fin 12) (Fin 12) (ZMod 2)) (X : Set (Fin 12 → ZMod 2)) :
    (fun v => v ᵥ* (A * B)) '' X = (fun v => v ᵥ* B) '' ((fun v => v ᵥ* A) '' X) := by
  rw [Set.image_image]
  simp only [Matrix.vecMul_vecMul]

theorem testBit_mask144 : ∀ p < 144,
    Nat.testBit (nat_lit 22300745198530623141535718272648361505980415) p = true := by
  decide +kernel

theorem letMat_lt (LET c : ℕ) : letMat LET c < 2 ^ 144 :=
  Nat.and_lt_two_pow _ (by decide +kernel)

theorem toMat_letMat (LET c : ℕ) (i j : Fin 12) :
    toMat (letMat LET c) i j = ((LET.testBit (144 * c + (12 * (i : ℕ) + j))).toNat : ZMod 2) := by
  rw [toMat_apply]
  change ((((LET >>> (144 * c)) &&& _).testBit _).toNat : ZMod 2) = _
  rw [Nat.testBit_and, testBit_mask144 _ (by omega), Bool.and_true, Nat.testBit_shiftRight]

@[expose] noncomputable def wordVal {M : Type*} [Monoid M] (e : ℕ → M) (w n : ℕ) : M :=
  Nat.rec (motive := fun _ => M) 1 (fun i acc => acc * e (wLet w i)) n

theorem wordVal_zero {M : Type*} [Monoid M] (e : ℕ → M) (w : ℕ) : wordVal e w 0 = 1 := rfl

theorem wordVal_succ {M : Type*} [Monoid M] (e : ℕ → M) (w n : ℕ) :
    wordVal e w (n + 1) = wordVal e w n * e (wLet w n) := rfl

theorem wordVal_eq_prod {M : Type*} [Monoid M] (e : ℕ → M) (w : ℕ) : ∀ n : ℕ,
    wordVal e w n = ((List.range n).map fun i => e (wLet w i)).prod
  | 0 => rfl
  | n + 1 => by
    rw [wordVal_succ, wordVal_eq_prod e w n, List.range_succ, List.map_append, List.prod_append]
    simp

theorem map_wordVal {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N]
    (f : F) (e : ℕ → M) (w : ℕ) : ∀ n : ℕ, f (wordVal e w n) = wordVal (fun c => f (e c)) w n
  | 0 => map_one f
  | n + 1 => by rw [wordVal_succ, wordVal_succ, map_mul, map_wordVal f e w n]

theorem evalW_lt (LET w : ℕ) : ∀ n : ℕ, evalW LET w n < 2 ^ 144
  | 0 => ident12_lt
  | _ + 1 => mul12_lt _ _

theorem toMat_evalW (LET w : ℕ) : ∀ n : ℕ,
    toMat (evalW LET w n) = wordVal (fun c => toMat (letMat LET c)) w n
  | 0 => toMat_ident12
  | n + 1 => by
    change toMat (mul12 (evalW LET w n) (letMat LET (wLet w n))) = _
    rw [toMat_mul12, toMat_evalW LET w n, wordVal_succ]

theorem chkEval_sound {LET w n M : ℕ} (h : chkEval LET w n M = true) :
    toMat M = wordVal (fun c => toMat (letMat LET c)) w n := by
  rw [← beq_eq_true.1 h, toMat_evalW]

end CFSG.KJ4.Mat

end
