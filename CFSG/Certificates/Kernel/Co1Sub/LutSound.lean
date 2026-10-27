module

public import CFSG.Certificates.Kernel.Co1Sub.SlpSound
import CFSG.Certificates.Kernel.Co1DceLemmas

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.TabMatGrp
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply toVecD_apply)

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

theorem MatP_apply (U : Nat) (i j : Fin 24) :
    MatP 24 U i j = if U.testBit (i.val * 24 + j.val) then 1 else 0 := by
  have hr : (unpackR 24 U)[i.val]?.getD 0 = rowF 24 U i.val := by
    simp [unpackR, i.isLt, rowF_eq]
  unfold MatP
  rw [rowsMatrix_apply, hr, toVecD_apply, testBit_rowF 24 _ _ _ j.isLt]

@[expose] def SL (k : Nat) (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Prop :=
  ∀ i j : Fin 24, i.val < j.val + k → M i j = 0

@[expose] def Low (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Prop := SL 1 (M - 1)

section Low

variable {M M' : Matrix (Fin 24) (Fin 24) (ZMod 2)}

theorem SL_mul {a b : Nat} (h : SL a M) (h' : SL b M') : SL (a + b) (M * M') := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : i.val < l.val + a
  · rw [h i l hl, zero_mul]
  · rw [h' l j (by omega), mul_zero]

theorem SL_add {a : Nat} (h : SL a M) (h' : SL a M') : SL a (M + M') := fun i j hij => by
  rw [Matrix.add_apply, h i j hij, h' i j hij, add_zero]

theorem SL_mono {a b : Nat} (hab : a ≤ b) (h : SL b M) : SL a M := fun i j hij =>
  h i j (by omega)

theorem SL_pow (h : SL 1 M) : ∀ k, SL k (M ^ k)
  | 0 => by
    rw [pow_zero]
    intro i j hij
    exact Matrix.one_apply_ne fun e => by rw [e] at hij; omega
  | k + 1 => by
    rw [pow_succ]
    exact SL_mul (SL_pow h k) h

theorem SL_24 (h : SL 24 M) : M = 0 := by
  ext i j
  rw [h i j (by have := i.isLt; omega), Matrix.zero_apply]

theorem sq_one_add (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : (1 + M) ^ 2 = 1 + M ^ 2 := by
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  have h2 : M + M = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact hz _
  calc (1 + M) ^ 2 = 1 + (M + M) + M ^ 2 := by noncomm_ring
    _ = 1 + M ^ 2 := by rw [h2, add_zero]

theorem Low_pow (h : Low M) : M ^ 32 = 1 := by
  have hN : (M - 1) ^ 24 = 0 := SL_24 (SL_pow h 24)
  have p2 : ∀ k : Nat, (1 + (M - 1)) ^ (2 ^ k) = 1 + (M - 1) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_one, pow_one]
    | succ k ih => rw [pow_succ, pow_mul, ih, sq_one_add, ← pow_mul]
  have e : M = 1 + (M - 1) := by abel
  have h32 : (M - 1) ^ (2 ^ 5) = 0 := by
    rw [(by norm_num : 2 ^ 5 = 24 + 8), pow_add, hN, zero_mul]
  have e32 : M ^ 32 = M ^ (2 ^ 5) := by norm_num
  rw [e32, e, p2 5, h32, add_zero]

theorem Low_one : Low (1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  unfold Low
  rw [sub_self]
  intro i j _
  rfl

theorem Low_mul (h : Low M) (h' : Low M') : Low (M * M') := by
  unfold Low at *
  have e : M * M' - 1 = (M - 1) * (M' - 1) + (M - 1) + (M' - 1) := by noncomm_ring
  rw [e]
  exact SL_add (SL_add (SL_mono (by norm_num) (SL_mul h h')) h) h'

theorem upM_bits : ∀ i j : Fin 24, i ≤ j → upM.testBit (i.val * 24 + j.val) = true := by
  decide +kernel

theorem oneS_bits : ∀ i j : Fin 24, oneS.testBit (i.val * 24 + j.val) = decide (i = j) := by
  decide +kernel

theorem Low_of_lutK {U : Nat} (h : lutK U = true) : Low (MatP 24 U) := by
  have e : U &&& upM = oneS := Nat.eq_of_beq_eq_true h
  intro i j hij
  have hij' : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
  have hb : U.testBit (i.val * 24 + j.val) = decide (i = j) := by
    rw [← oneS_bits i j, ← e, Nat.testBit_and, upM_bits i j hij', Bool.and_true]
  rw [Matrix.sub_apply, Matrix.one_apply, MatP_apply, hb]
  by_cases h' : i = j
  · simp [h']
  · simp [h']

theorem conj_pow {B Bi U : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : Bi * B = 1) (h' : B * Bi = 1) :
    ∀ n : Nat, (B * U * Bi) ^ n = B * U ^ n * Bi
  | 0 => by rw [pow_zero, pow_zero, mul_one, h']
  | n + 1 => by
    rw [pow_succ, conj_pow h h' n, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc Bi B, h, one_mul]

end Low

theorem allN_iff' (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem shiftRight_one_eq_six (n : Nat) : n.shiftRight 6 = n / 64 := by
  change n >>> 6 = n / 64
  rw [Nat.shiftRight_eq_div_pow]

theorem flagAt_spec {gens : List Nat} {P0 : Nat} {P Pi R : List Nat}
    (h : flagK gens P0 P Pi R = true) {k : Nat} (hk : k < P.length) :
    mulS (P.getD k 0) (Pi.getD k 0) = oneS ∧ ∀ t < gens.length, ∃ j < P.length,
      lutK (mulS (mulS (P.getD k 0) (gens.getD t 0)) (Pi.getD j 0)) = true := by
  unfold flagK at h
  rw [strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨-, -, h3⟩ := h
  have hN : lenL P ≤ 64 * Nat.succ (Nat.shiftRight (lenL P) 6) := by
    rw [lenL_eq_length, shiftRight_one_eq_six]
    omega
  have hk' := CFSG.Certificates.Co1D.allBelow_spec h3 hN k (by rw [lenL_eq_length]; exact hk)
  unfold flagAt at hk'
  rw [strictB_eq, strictB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hk'
  obtain ⟨h1, h2, -⟩ := hk'
  rw [getL_zero_eq, getL_zero_eq] at h1
  refine ⟨Nat.eq_of_beq_eq_true h1, fun t ht => ?_⟩
  have h2' := (allN_iff' _ _).1 h2 t (by rw [lenL_eq_length]; exact ht)
  rw [strictB_eq, andB_eq, Bool.and_eq_true] at h2'
  simp only [getL_zero_eq, lenL_eq_length] at h2'
  exact ⟨_, Nat.blt_eq.mp h2'.1, h2'.2⟩

variable {G : Type*} [Group G] {φ : G →* GL (Fin 24) (ZMod 2)}

theorem pow32_of_flag (hφ : Function.Injective φ) {base : ℕ → G} {gens : List Nat}
    (hg : ∀ i < gens.length, MatP 24 (gens.getD i 0) = matOf φ (base i)) {P0 : Nat}
    {P Pi R : List Nat} (h : flagK gens P0 P Pi R = true) (h1 : P.length = 1) :
    ∀ x ∈ Subgroup.closure {g | ∃ i < gens.length, base i = g}, x ^ 32 = 1 := by
  obtain ⟨hPP, hgen⟩ := flagAt_spec h (k := 0) (by omega)
  set B := MatP 24 (P.getD 0 0)
  set Bi := MatP 24 (Pi.getD 0 0)
  have hBB : B * Bi = 1 := by
    rw [← MatP_mul, ← mulS_eq, hPP, MatP_oneS]
  have hBB' : Bi * B = 1 := (mul_eq_one_comm (M := Matrix (Fin 24) (Fin 24) (ZMod 2))).mp hBB
  have hconj : ∀ x y : G, B * matOf φ (x * y) * Bi =
      (B * matOf φ x * Bi) * (B * matOf φ y * Bi) := fun x y => by
    rw [matOf_mul]
    simp only [mul_assoc]
    rw [← mul_assoc Bi B, hBB', one_mul]
  have hpow : ∀ x : G, Low (B * matOf φ x * Bi) → x ^ 32 = 1 := fun x hx => by
    have e := Low_pow hx
    have mp : matOf φ (x ^ 32) = matOf φ x ^ 32 := by simp [matOf]
    rw [conj_pow hBB' hBB, ← mp] at e
    have e' : matOf φ (x ^ 32) = 1 := by
      calc matOf φ (x ^ 32) = Bi * (B * matOf φ (x ^ 32) * Bi) * B := by
            simp only [mul_assoc]
            rw [hBB', mul_one, ← mul_assoc, hBB', one_mul]
        _ = 1 := by rw [e, mul_one, hBB']
    exact hφ (Units.ext (by rw [map_one]; exact e'))
  suffices ∀ x ∈ Subgroup.closure {g | ∃ i < gens.length, base i = g}, Low (B * matOf φ x * Bi)
    from fun x hx => hpow x (this x hx)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, hl⟩ := hgen i hi
    have hj0 : j = 0 := by omega
    subst hj0
    have := Low_of_lutK hl
    rwa [mulS_eq, MatP_mul, mulS_eq, MatP_mul, hg i hi] at this
  | one =>
    rw [matOf_one, mul_one, hBB]
    exact Low_one
  | mul y z _ _ hy hz =>
    rw [hconj]
    exact Low_mul hy hz
  | inv y _ hy =>
    have e32 := hpow y hy
    have hinv : y⁻¹ = y ^ 31 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact e32
    rw [hinv]
    have : ∀ n : Nat, Low (B * matOf φ (y ^ n) * Bi) := by
      intro n
      induction n with
      | zero =>
        rw [pow_zero, matOf_one, mul_one, hBB]
        exact Low_one
      | succ n ih =>
        rw [pow_succ, hconj]
        exact Low_mul ih hy
    exact this 31

end CFSG.KC.Co1Sub

end
