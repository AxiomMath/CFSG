module

public import Certificates.Data.Kernel.Spor.Fi24FixP
public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Certificates.Kernel.LceSP.Popcount
public import CFSG.Certificates.Kernel.LceSP.Base
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.Fi24FixP

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24FixP
  CFSG.Certificates.LceP Finset

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem popcount_19 (x : ℕ) : popcount x 524288 = ∑ j ∈ range 524288, x / 2 ^ j % 2 := by
  set x1 := swarStep 524288 1 x
  set x2 := swarStep 524288 2 x1
  set x3 := swarStep 524288 4 x2
  set x4 := swarStep 524288 8 x3
  have c1 : ds 2 x1 262144 = ds 1 x 524288 :=
    ds_swarStep (b := 1) (b2 := 2) (m := 262144) (m2 := 524288) (n := 524288) (by norm_num) rfl
      rfl rfl x
  have c2 : ds 4 x2 131072 = ds 2 x1 262144 :=
    ds_swarStep (b := 2) (b2 := 4) (m := 131072) (m2 := 262144) (n := 524288) (by norm_num) rfl
      rfl rfl x1
  have c3 : ds 8 x3 65536 = ds 4 x2 131072 :=
    ds_swarStep (b := 4) (b2 := 8) (m := 65536) (m2 := 131072) (n := 524288) (by norm_num) rfl
      rfl rfl x2
  have c4 : ds 16 x4 32768 = ds 8 x3 65536 :=
    ds_swarStep (b := 8) (b2 := 16) (m := 32768) (m2 := 65536) (n := 524288) (by norm_num) rfl
      rfl rfl x3
  have hrep := swarStep_rep (b := 16) (b2 := 32) (m := 16384) (n := 524288) (by norm_num) rfl rfl x4
  set e : ℕ → ℕ := fun t => x4 / 2 ^ (16 * (2 * t)) % 2 ^ 16 + x4 / 2 ^ (16 * (2 * t + 1)) % 2 ^ 16
  have hT : ∑ t ∈ range (16383 + 1), e t = ds 1 x 524288 := by
    rw [← c1, ← c2, ← c3, ← c4]
    unfold ds
    exact sum_pairs (fun j => x4 / 2 ^ (16 * j) % 2 ^ 16) 16384
  have hTle : ∑ t ∈ range (16383 + 1), e t ≤ 524288 := by
    rw [hT]
    exact ds_one_le x 524288
  obtain ⟨Lw, Hh, hm, hL⟩ := mul_gs (2 ^ 32) 16383 e
  have h3 : (2 : ℕ) ^ 32 = 4294967295 + 1 := by norm_num
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 524288) 1) 4294967295 = gs (2 ^ 32) 16384 := by
    rw [h3]
    exact gs_shl 4294967295 16384 524288 (by norm_num) (by rw [← h3, ← pow_mul])
  generalize hX : (2 : ℕ) ^ 32 = X at hm hL hG
  have hX1 : X = 4294967295 + 1 := by rw [← hX, h3]
  have hLw : Lw < X ^ 16383 := by
    have h1 := gs_mul 4294967295 16383
    rw [← hX1] at h1
    have h2 : Lw ≤ 4294967295 * gs X 16383 :=
      le_trans hL (Nat.mul_le_mul_right _ (by omega))
    omega
  change Nat.land (Nat.shiftRight (Nat.mul (swarStep 524288 16 x4)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 524288) 1) 4294967295)) (Nat.sub 524288 32)) 4294967295 = _
  rw [hG]
  change (swarStep 524288 16 x4 * gs X 16384) >>> (32 * 16383) &&& (2 ^ 32 - 1) = _
  rw [hrep, Nat.and_two_pow_sub_one_eq_mod, shr32, hX]
  change (∑ t ∈ range (16383 + 1), e t * X ^ t) * gs X (16383 + 1) / X ^ 16383 % X = _
  rw [hm]
  have e2 : Lw + X ^ 16383 * (∑ t ∈ range (16383 + 1), e t) + X ^ (16383 + 1) * Hh =
      Lw + X ^ 16383 * ((∑ t ∈ range (16383 + 1), e t) + X * Hh) := by ring
  have hX0 : 0 < X := by
    rw [hX1]
    exact Nat.succ_pos _
  have hpos : 0 < X ^ 16383 := pow_pos hX0 _
  rw [e2, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hLw, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), hT, ds_one]

theorem sum_bits (x N : ℕ) :
    ∑ j ∈ range N, x / 2 ^ j % 2 = #((range N).filter (fun j => x.testBit j = true)) := by
  rw [card_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

variable {A σ : Nat → Nat → Nat}

theorem foldr_lt : ∀ (w : List Nat), (∀ l ∈ w, ∀ q, q < 524288 → σ l q < 524288) →
    ∀ q, q < 524288 → w.foldr σ q < 524288
  | [], _, _, h => h
  | l :: w, hσ, q, h =>
    hσ l List.mem_cons_self _ (foldr_lt w (fun l' hl' => hσ l' (List.mem_cons_of_mem _ hl')) q h)

theorem testBit_walkP : ∀ (w : List Nat), (∀ l ∈ w, ∀ q, q < 524288 → σ l q < 524288) →
    (∀ l ∈ w, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (σ l q)) →
    ∀ v q, q < 524288 → (walkP A w v).testBit q = v.testBit (w.foldr σ q)
  | [], _, _, _, _, _ => rfl
  | l :: w, hσ, hA, v, q, hq => by
    have hσ' : ∀ l' ∈ w, ∀ q, q < 524288 → σ l' q < 524288 :=
      fun l' hl' => hσ l' (List.mem_cons_of_mem _ hl')
    have e : walkP A (l :: w) v = walkP A w (A l v) := strictN_eq _ _
    rw [e, testBit_walkP w hσ' (fun l' hl' => hA l' (List.mem_cons_of_mem _ hl')) _ q hq,
      hA l List.mem_cons_self _ _ (foldr_lt w hσ' q hq)]
    rfl

theorem testBit_idPl19 {k : Nat} (hk : k < 19) (p : Nat) :
    (idPl19 k).testBit p = (decide (p < 524288) && p.testBit k) :=
  idPlane_testBit (k := 19) hk p

theorem testBit_ones (W i : Nat) : (ones W).testBit i = decide (i < W) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

section Fix

variable {F : Nat → Nat} {g : Nat → Nat}
  (hF : ∀ v q, q < 524288 → (F v).testBit q = v.testBit (g q))
  (hg : ∀ q, q < 524288 → g q < 524288)
include hF hg

theorem testBit_plane {k : Nat} (hk : k < 19) {x : Nat} (hx : x < 524288) :
    (nIf(Nat.beq k (nat_lit 0), F (idPl19 (nat_lit 0)),
      Nat.xor (F (Nat.xor (idPl19 k) (idPl19 (nat_lit 0)))) (F (idPl19 (nat_lit 0))))).testBit x =
      (g x).testBit k := by
  have hgx := hg x hx
  by_cases k0 : k = 0
  · subst k0
    change (F (idPl19 0)).testBit x = _
    rw [hF _ _ hx, testBit_idPl19 (by decide), decide_eq_true hgx, Bool.true_and]
  · have hb : Nat.beq k 0 = false := by
      cases h : Nat.beq k 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) k0
    rw [hb]
    change ((F ((idPl19 k) ^^^ (idPl19 0))) ^^^ (F (idPl19 0))).testBit x = _
    rw [Nat.testBit_xor, hF _ _ hx, hF _ _ hx, Nat.testBit_xor, testBit_idPl19 hk,
      testBit_idPl19 (by decide), decide_eq_true hgx, Bool.true_and, Bool.true_and,
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem testBit_fixStep {k : Nat} (hk : k < 19) (a : Nat) {x : Nat} (hx : x < 524288) :
    (fixStep F (F (idPl19 (nat_lit 0))) k a).testBit x =
      (a.testBit x && ((g x).testBit k == x.testBit k)) := by
  unfold fixStep
  have hp := testBit_plane hF hg hk hx
  change (a &&& ((ones 524288) ^^^ ((nIf(Nat.beq k (nat_lit 0), F (idPl19 (nat_lit 0)),
      Nat.xor (F (Nat.xor (idPl19 k) (idPl19 (nat_lit 0)))) (F (idPl19 (nat_lit 0))))) ^^^
      (idPl19 k)))).testBit x = _
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, hp, testBit_ones, decide_eq_true hx,
    testBit_idPl19 hk, decide_eq_true hx, Bool.true_and]
  cases (g x).testBit k <;> cases x.testBit k <;> rfl

omit hF hg in
theorem fixAcc_succ (P0 k : Nat) : fixAcc F P0 (k + 1) = fixStep F P0 k (fixAcc F P0 k) :=
  strictN_eq _ _

omit hF hg in
theorem fixAcc_lt (P0 x : Nat) : ∀ k, (fixAcc F P0 k).testBit x = true → x < 306936
  | 0, h => by
    change (ones 306936).testBit x = true at h
    rw [testBit_ones] at h
    exact of_decide_eq_true h
  | k + 1, h => by
    rw [fixAcc_succ] at h
    unfold fixStep at h
    rw [nland, Nat.testBit_and, Bool.and_eq_true] at h
    exact fixAcc_lt P0 x k h.1

theorem testBit_fixAcc {x : Nat} (hx : x < 524288) : ∀ k, k ≤ 19 →
    ((fixAcc F (F (idPl19 (nat_lit 0))) k).testBit x = true ↔
      x < 306936 ∧ ∀ k' < k, (g x).testBit k' = x.testBit k')
  | 0, _ => by
    change (ones 306936).testBit x = true ↔ _
    rw [testBit_ones]
    simp
  | k + 1, hk => by
    rw [fixAcc_succ, testBit_fixStep hF hg (by omega) _ hx, Bool.and_eq_true,
      testBit_fixAcc hx k (by omega), beq_iff_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun k' hk' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
      · exact h2 k' h
      · rw [h]
        exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun k' hk' => h2 k' (by omega)⟩, h2 k (by omega)⟩

theorem testBit_fixS (x : Nat) : (fixS F).testBit x = true ↔ x < 306936 ∧ g x = x := by
  have e : fixS F = fixAcc F (F (idPl19 (nat_lit 0))) 19 := strictN_eq _ _
  rw [e]
  by_cases hx : x < 524288
  · rw [testBit_fixAcc hF hg hx 19 (Nat.le_refl _)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Nat.eq_of_testBit_eq fun i => ?_⟩
      by_cases hi : i < 19
      · exact h2 i hi
      · have h19 : (524288 : Nat) ≤ 2 ^ i :=
          Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_lt hi)
        rw [Nat.testBit_lt_two_pow (by have := hg x hx; omega),
          Nat.testBit_lt_two_pow (by omega)]
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k' _ => by rw [h2]⟩
  · constructor
    · intro h
      have := fixAcc_lt (F := F) _ x 19 h
      omega
    · rintro ⟨h, -⟩
      omega

theorem popcount_fixS :
    popcount (fixS F) 524288 = #((range 306936).filter fun x => g x = x) := by
  have e : (range 524288).filter (fun j => (fixS F).testBit j = true) =
      (range 306936).filter fun x => g x = x := by
    ext x
    rw [mem_filter, mem_filter, mem_range, mem_range, testBit_fixS hF hg]
    omega
  rw [popcount_19, sum_bits, e]

end Fix

theorem fixOK_spec {w : List Nat} (hσ : ∀ l ∈ w, ∀ q, q < 524288 → σ l q < 524288)
    (hA : ∀ l ∈ w, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (σ l q)) {c : Nat}
    (h : fixOK A w c = true) :
    #((range 306936).filter fun x => w.foldr σ x = x) = c := by
  unfold fixOK at h
  rw [← popcount_fixS (F := walkP A w) (testBit_walkP w hσ hA) (foldr_lt w hσ)]
  exact Nat.eq_of_beq_eq_true h

end CFSG.KS.Fi24FixP

end
