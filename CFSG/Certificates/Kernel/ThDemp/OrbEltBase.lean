
module

public import CFSG.Certificates.Kernel.ThDemp.OrbCentBase
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace CFSG.Certificates.ThDemp.Elt

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.Cent

set_option exponentiation.threshold 2000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

theorem mat_pow (g : J) (n : ℕ) : 𝕄 (g ^ n) = (𝕄 g) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem chainEl_eq (e : ℕ) : chainEl D e = D.mul (D.mul (D.mul (D.mul (D.mul (D.mul D.ONE
    (D.stepY 5 (bitsN e 40 8) D.ONE)) (D.stepY 4 (bitsN e 32 8) D.ONE))
    (D.stepY 3 (bitsN e 24 8) D.ONE)) (D.stepY 2 (bitsN e 16 8) D.ONE))
    (D.stepY 1 (bitsN e 8 8) D.ONE)) (D.stepY 0 (bitsN e 0 8) D.ONE) := by
  unfold chainEl
  simp only [strictN_eq]

theorem codeChk_sound {e : ℕ} (h : codeChk D e = true) : ∀ l < 6, bitsN e (8 * l) 8 < D.oszL l :=
  fun l hl => Nat.blt_eq.mp (Unfold.allBelow_spec h (by norm_num) l hl)

noncomputable def coordsOf (e : ℕ) : Coords :=
  (⟨bitsN e 0 8 % 31, Nat.mod_lt _ (by norm_num)⟩, ⟨bitsN e 8 8 % 30, Nat.mod_lt _ (by norm_num)⟩,
    ⟨bitsN e 16 8 % 28, Nat.mod_lt _ (by norm_num)⟩, ⟨bitsN e 24 8 % 24, Nat.mod_lt _ (by norm_num)⟩,
    ⟨bitsN e 32 8 % 16, Nat.mod_lt _ (by norm_num)⟩, ⟨bitsN e 40 8 % 32, Nat.mod_lt _ (by norm_num)⟩)

structure Elt1Facts (D : DempData) (O : OrbData) : Prop where
  words : wordsChk D O = true
  g0 : combChk D.rm (mulB (cR 5) D.rm (U0 D) (gen D 0)) (U0 D) O.gd0 = true
  g1 : combChk D.rm (mulB (cR 5) D.rm (U0 D) (gen D 1)) (U0 D) O.gd1 = true
  nd : nodupB (combsL (rowsOf D.rm (U0 D)) 0) = true
  o5 : ordChk D (chainEl D O.x5) 5 = true
  o31 : ordChk D (chainEl D O.x31) 31 = true
  ob : ordChk D (chainEl D O.yb) 31 = true
  ga : combChk D.rm (mulB (cR 5) D.rm (pt D O 7) (chainEl D O.x31)) (pt D O 7) O.Ga = true
  gb : combChk D.rm (mulB (cR 5) D.rm (pt D O 8) (chainEl D O.yb)) (pt D O 8) O.Gb = true

theorem eltChk1_facts (h : eltChk1 D O = true) : Elt1Facts D O := by
  unfold eltChk1 at h
  obtain ⟨hw, h⟩ := Unfold.andB_split h
  obtain ⟨g0, h⟩ := Unfold.andB_split h
  obtain ⟨g1, h⟩ := Unfold.andB_split h
  obtain ⟨nd, h⟩ := Unfold.andB_split h
  obtain ⟨o5, h⟩ := Unfold.andB_split h
  obtain ⟨o31, h⟩ := Unfold.andB_split h
  obtain ⟨ob, h⟩ := Unfold.andB_split h
  obtain ⟨ga, gb⟩ := Unfold.andB_split h
  exact ⟨hw, g0, g1, nd, o5, o31, ob, ga, gb⟩

theorem orderOf_of_mat {H : Subgroup J} (x : H) {X p : ℕ} (hx : 𝕄 (x : J) = pkMat X)
    (hp : p.Prime) (h : pkMat X ^ p = 1 ∧ pkMat X ≠ 1) : orderOf x = p := by
  have := Fact.mk hp
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    apply FwdRel.mat_injective
    change 𝕄 ((x : J) ^ p) = 𝕄 (1 : J)
    rw [mat_pow, hx, h.1]
    rfl
  · intro h1
    apply h.2
    rw [← hx, h1]
    rfl

namespace Ctx

end Ctx

noncomputable def Qm (q : ℕ) (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) :
    Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  M ^ 5 + ∑ j ∈ Finset.range 5, ((bitsN q j 1 : ℕ) : ZMod 2) • M ^ j

def KillU (D : DempData) (N : Matrix (Fin 248) (Fin 248) (ZMod 2)) : Prop :=
  ∀ w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)), Matrix.vecMul w N = 0

theorem pow_semiconj {A M N : Matrix (Fin 248) (Fin 248) (ZMod 2)} (h : A * M = N * A) :
    ∀ j : ℕ, A * M ^ j = N ^ j * A
  | 0 => by rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
  | j + 1 => by
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, pow_semiconj h j, Matrix.mul_assoc, h,
      ← Matrix.mul_assoc]

theorem Qm_semiconj (q : ℕ) {A M N : Matrix (Fin 248) (Fin 248) (ZMod 2)} (h : A * M = N * A) :
    A * Qm q M = Qm q N * A := by
  unfold Qm
  rw [Matrix.mul_add, Matrix.add_mul, pow_semiconj h 5, Finset.mul_sum, Finset.sum_mul]
  refine congrArg (N ^ 5 * A + ·) (Finset.sum_congr rfl fun j _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, pow_semiconj h j]

private def qRow (P r : ℕ) : ℕ := (P >>> (256 * r)) &&& (2 ^ 248 - 1)

private theorem testBit_qRow (P r j : ℕ) :
    (qRow P r).testBit j = (P.testBit (256 * r + j) && decide (j < 248)) := by
  rw [qRow, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

private theorem qRow_xor (A B r : ℕ) : qRow (A ^^^ B) r = qRow A r ^^^ qRow B r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_qRow, testBit_qRow, testBit_qRow, Nat.testBit_xor]
  cases A.testBit (256 * r + j) <;> cases B.testBit (256 * r + j) <;> cases decide (j < 248) <;> rfl

private theorem qRow_zero (r : ℕ) : qRow 0 r = 0 := by
  rw [qRow, Nat.zero_shiftRight, Nat.zero_and]

private theorem qRow_bit {t : ℕ} (ht : t < 2) (A r : ℕ) : qRow (t * A) r = t * qRow A r := by
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [Nat.zero_mul, Nat.zero_mul, qRow_zero]
  · rw [Nat.one_mul, Nat.one_mul]

private def QFits (P : ℕ) : Prop := ∀ p, P.testBit p = true → p % 256 < 248 ∧ p / 256 < 5

private theorem qFits_mulB (A B : ℕ) : QFits (mulB (rep 1 256 5) (2 ^ 248 - 1) A B) := by
  intro p hp
  rw [testBit_mulB_rows, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.1

private theorem QFits.xor {A B : ℕ} (hA : QFits A) (hB : QFits B) : QFits (A ^^^ B) := by
  intro p hp
  rw [Nat.testBit_xor] at hp
  cases hA' : A.testBit p
  · rw [hA', Bool.false_xor] at hp
    exact hB p hp
  · exact hA p hA'

private theorem QFits.bit {t A : ℕ} (ht : t < 2) (hA : QFits A) : QFits (t * A) := by
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · intro p hp
    rw [Nat.zero_mul, Nat.zero_testBit] at hp
    exact absurd hp (by decide)
  · rwa [Nat.one_mul]

private theorem QFits.lt {A : ℕ} (hA : QFits A) : A < 2 ^ 1280 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_contra h
  have := (hA i (by simpa using h)).2
  omega

private theorem QFits.eq_zero {A : ℕ} (hA : QFits A) (h : ∀ r < 5, qRow A r = 0) : A = 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.zero_testBit]
  by_contra hp
  have hp' : A.testBit p = true := by simpa using hp
  obtain ⟨h1, h2⟩ := hA p hp'
  have := congrArg (fun n => n.testBit (p % 256)) (h (p / 256) h2)
  simp only [testBit_qRow, Nat.zero_testBit] at this
  rw [Nat.div_add_mod, hp', decide_eq_true h1] at this
  exact absurd this (by decide)

private noncomputable def qPow (D : DempData) (Y X : ℕ) : ℕ → ℕ
  | 0 => X
  | m + 1 => mulB (cR 5) D.rm (qPow D Y X m) Y

private theorem qFits_qPow (hrm : D.rm = 2 ^ 248 - 1) (Y : ℕ) {X : ℕ} (hX : QFits X) :
    ∀ m, QFits (qPow D Y X m)
  | 0 => hX
  | m + 1 => by
    show QFits (mulB (cR 5) D.rm (qPow D Y X m) Y)
    rw [hrm, cR_eq]
    exact qFits_mulB _ _

private theorem powStack_eq (hrm : D.rm = 2 ^ 248 - 1) (Y : ℕ) {X : ℕ} (hX : QFits X) :
    ∀ n, powStack D Y X n = stackN 1280 (n + 1) (qPow D Y X)
  | 0 => by
    show X = 0 ||| X <<< (1280 * 0)
    rw [Nat.mul_zero, Nat.shiftLeft_zero, Nat.zero_or]
  | n + 1 => by
    show strictN (powStack D Y X n) (fun S' => S' ||| mulB (cR 5) D.rm (ptAt S' n) Y <<<
      (1280 * (n + 1))) =
      stackN 1280 (n + 1) (qPow D Y X) ||| qPow D Y X (n + 1) <<< (1280 * (n + 1))
    simp only [strictN_eq]
    rw [powStack_eq hrm Y hX n, ptAt_eq,
      lane_stackN (fun k => (qFits_qPow hrm Y hX k).lt) (Nat.lt_succ_self n)]
    rfl

private theorem ptAt_powStack (hrm : D.rm = 2 ^ 248 - 1) (Y : ℕ) {X : ℕ} (hX : QFits X) {i : ℕ}
    (hi : i < 31) : ptAt (powStack D Y X 30) i = qPow D Y X i := by
  rw [powStack_eq hrm Y hX, ptAt_eq, lane_stackN (fun k => (qFits_qPow hrm Y hX k).lt) (by omega)]

private theorem pkVec_qRow_qPow (hrm : D.rm = 2 ^ 248 - 1) (hbv : ∀ l < 5, D.bvL l < 2 ^ 248)
    (Y : ℕ) {r : ℕ} (hr : r < 5) :
    ∀ m, pkVec (qRow (qPow D Y (U0 D) m) r) = Matrix.vecMul (pkVec (D.bvL r)) (pkMat Y ^ m)
  | 0 => by
    rw [pow_zero, Matrix.vecMul_one]
    show pkVec ((U0 D >>> (256 * r)) &&& (2 ^ 248 - 1)) = _
    rw [U0, row_stackN hbv hr]
  | m + 1 => by
    have e : qRow (qPow D Y (U0 D) (m + 1)) r =
        vecB (2 ^ 248 - 1) (qRow (qPow D Y (U0 D) m) r) Y := by
      show qRow (mulB (cR 5) D.rm (qPow D Y (U0 D) m) Y) r = _
      rw [hrm, cR_eq]
      exact row_mulB hr _ _
    rw [e, pkVec_vecB', pkVec_qRow_qPow hrm hbv Y hr m, Matrix.vecMul_vecMul, pow_succ]

private theorem pow_mod_31 {M : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hM : M ^ 31 = 1) (j k : ℕ) :
    M ^ (j * k % 31) = (M ^ k) ^ j := by
  rw [← pow_mul, Nat.mul_comm k j]
  conv_rhs => rw [← Nat.div_add_mod (j * k) 31, pow_add, pow_mul, hM, one_pow, one_mul]

private noncomputable def qPart (q k L : ℕ) : ℕ → ℕ
  | 0 => ptAt L (5 * k % 31)
  | n + 1 => qPart q k L n ^^^ bitsN q n 1 * ptAt L (n * k % 31)

private theorem qRows_eq (q k L : ℕ) : qRows q k L = qPart q k L 5 := rfl

private theorem killU_iff (hbv : ∀ l < 5, D.bvL l < 2 ^ 248)
    (N : Matrix (Fin 248) (Fin 248) (ZMod 2)) :
    KillU D N ↔ ∀ r < 5, Matrix.vecMul (pkVec (D.bvL r)) N = 0 := by
  constructor
  · intro h r hr
    apply h
    rw [sp, rowsOf_U0 hbv, spanL]
    apply Submodule.subset_span
    refine ⟨D.bvL r, ?_, rfl⟩
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp
  · intro h w hw
    rw [sp, rowsOf_U0 hbv, spanL] at hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, hb, rfl⟩ := hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl
      exacts [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)]
    | zero => exact Matrix.zero_vecMul _
    | add x y _ _ hx hy => rw [Matrix.add_vecMul, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_vecMul, hx, smul_zero]

theorem mem_zpowers_of_card {S : Type*} [Group S] [Finite S] (hS : Nat.card S = 155) {y t : S}
    (hy : orderOf y = 31) (ht : orderOf t = 31) : t ∈ Subgroup.zpowers y := by
  set H := Subgroup.zpowers y
  have hH : Nat.card H = 31 := by rw [Nat.card_zpowers, hy]
  have hidx : H.index = 5 := by
    have := Subgroup.card_mul_index H
    rw [hH, hS] at this
    omega
  have hmin : (Nat.card S).minFac = 5 := by rw [hS]; norm_num
  have hn : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  have h1 : orderOf (QuotientGroup.mk t : S ⧸ H) ∣ 31 := by
    rw [← ht]
    exact orderOf_map_dvd (QuotientGroup.mk' H) t
  have h2 : orderOf (QuotientGroup.mk t : S ⧸ H) ∣ 5 := by
    rw [← hidx]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk t : S ⧸ H) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rw [(by norm_num : Nat.gcd 31 5 = 1)] at this
    exact Nat.dvd_one.mp this
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.Certificates.ThDemp.Elt

end
