module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Certificates.Data.Kernel.LyOmega.Base
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section
namespace CFSG.KS.LyOm.SB2
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem bEnt_eq (X i j : ℕ) : bEnt X i j = X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 := by
  unfold bEnt fldW
  show (X >>> (1332 * i + 12 * j)) &&& ((1 <<< 12) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem bEnt_lt (X i j : ℕ) : bEnt X i j < 2 ^ 12 := by
  rw [bEnt_eq]; exact Nat.mod_lt _ (by positivity)

private noncomputable def inner (X i J : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (bEnt X i j) (1332 * j + 12 * i))) J

private noncomputable def outer (X I : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (inner X i 111)) I

private theorem fTr_eq (X : ℕ) : fTr X = outer X 111 := by
  have h : ∀ n, (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => CFSG.KC.Loop.strictN acc (fun a => Nat.lor a (inner X i 111))) n : ℕ) =
      outer X n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show CFSG.KC.Loop.strictN _ _ = _
      rw [strictN_eq', ih]; rfl
  exact h 111

private theorem tb_shift (a s b : ℕ) (ha : a < 2 ^ 12) (J i : ℕ) (hs : s = 1332 * J + 12 * i)
    (hi : i < 111) :
    Nat.testBit (Nat.shiftLeft a s) b =
      (decide (b / 1332 = J ∧ b % 1332 / 12 = i) && Nat.testBit a (b % 12)) := by
  show Nat.testBit (a <<< s) b = _
  rw [Nat.testBit_shiftLeft]
  by_cases h : b / 1332 = J ∧ b % 1332 / 12 = i
  · have h1 : s ≤ b := by omega
    have h2 : b - s = b % 12 := by omega
    simp [h, h1, h2]
  · have : ¬ (s ≤ b ∧ b - s < 12) := by omega
    by_cases h1 : s ≤ b
    · have h3 : 12 ≤ b - s := by omega
      have : Nat.testBit a (b - s) = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) h3)
      simp [h, h1, this]
    · simp [h, h1]

private theorem inner_tb (X i : ℕ) (hi : i < 111) (J : ℕ) (b : ℕ) :
    Nat.testBit (inner X i J) b =
      (decide (b / 1332 < J ∧ b % 1332 / 12 = i) && Nat.testBit (bEnt X i (b / 1332)) (b % 12)) := by
  induction J with
  | zero => simp [inner]
  | succ J ih =>
    have e : inner X i (J + 1) = Nat.lor (inner X i J)
        (Nat.shiftLeft (bEnt X i J) (1332 * J + 12 * i)) := rfl
    rw [e, Nat.lor_eq, Nat.testBit_or, ih, tb_shift _ _ _ (bEnt_lt X i J) J i rfl hi]
    by_cases h : b / 1332 = J ∧ b % 1332 / 12 = i
    · obtain ⟨h1, h2⟩ := h
      simp [h1, h2]
    · by_cases h1 : b / 1332 = J
      · have : ¬ b % 1332 / 12 = i := fun h2 => h ⟨h1, h2⟩
        simp [h1, this]
      · have : (b / 1332 < J + 1 ↔ b / 1332 < J) := by omega
        simp [h, this]

private theorem outer_tb (X : ℕ) (I : ℕ) (hI : I ≤ 111) (b : ℕ) :
    Nat.testBit (outer X I) b =
      (decide (b / 1332 < 111 ∧ b % 1332 / 12 < I) &&
        Nat.testBit (bEnt X (b % 1332 / 12) (b / 1332)) (b % 12)) := by
  induction I with
  | zero => simp [outer]
  | succ I ih =>
    have e : outer X (I + 1) = Nat.lor (outer X I) (inner X I 111) := rfl
    rw [e, Nat.lor_eq, Nat.testBit_or, ih (by omega), inner_tb X I (by omega)]
    by_cases h : b % 1332 / 12 = I
    · have : ¬ b % 1332 / 12 < I := by omega
      have h' : (b % 1332 / 12 < I + 1) := by omega
      simp [h, this, h']
    · by_cases h2 : b % 1332 / 12 < I
      · have : (b % 1332 / 12 < I + 1) := by omega
        simp [h, h2, this]
      · have : ¬ (b % 1332 / 12 < I + 1) := by omega
        simp [h, h2, this]

private theorem lane_tb (X i j t : ℕ) (hi : i < 111) (hj : j < 111) (ht : t < 12) :
    Nat.testBit (fTr X) (1332 * j + 12 * i + t) = Nat.testBit (bEnt X i j) t := by
  rw [fTr_eq, outer_tb X 111 le_rfl]
  have h1 : (1332 * j + 12 * i + t) / 1332 = j := by omega
  have h2 : (1332 * j + 12 * i + t) % 1332 / 12 = i := by omega
  have h3 : (1332 * j + 12 * i + t) % 12 = t := by omega
  rw [h1, h2, h3]
  simp [hi, hj]

private theorem lane_eq (X i j : ℕ) (hi : i < 111) (hj : j < 111) :
    fTr X / 2 ^ (1332 * j + 12 * i) % 2 ^ 12 = bEnt X i j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < 12
  · have := lane_tb X i j t hi hj ht
    simp only [ht, decide_true, Bool.true_and]
    rw [add_comm t (1332 * j + 12 * i), this]
  · have : Nat.testBit (bEnt X i j) t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (bEnt_lt X i j) (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [ht, this]

theorem fTr_sound {X : ℕ} (hX : LCanon 12 111 111 X) :
    LCanon 12 111 111 (fTr X) ∧ bigM (fTr X) = (bigM X).transpose := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro b hb
    rw [fTr_eq, outer_tb X 111 le_rfl]
    have : ¬ (b / 1332 < 111 ∧ b % 1332 / 12 < 111) := by omega
    simp [this]
  · intro i hi j hj
    have := lane_eq X j i hj hi
    have e : 12 * 111 * i + 12 * j = 1332 * i + 12 * j := by ring
    rw [e, this, bEnt_eq]
    have := hX.2 j hj i hi
    have e2 : 12 * 111 * j + 12 * i = 1332 * j + 12 * i := by ring
    rwa [e2] at this
  · funext i j
    simp only [bigM, ent, Matrix.transpose_apply]
    rw [lane_eq X j i j.2 i.2, bEnt_eq]

end CFSG.KS.LyOm.SB2
end
