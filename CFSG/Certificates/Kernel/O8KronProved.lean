module

public import Certificates.Data.Kernel.O8.EnumK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Bridge

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem testBit_orN_iff (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = true ↔ ∃ i < n, (f i).testBit p = true
  | 0 => by
    have e : orN 0 f = 0 := rfl
    simp [e]
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, testBit_orN_iff f p n]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem beq_bitN (x q : ℕ) : Nat.beq (bitN x q) 1 = x.testBit q := by
  unfold bitN
  change Nat.beq ((x >>> q) &&& 1) 1 = _
  have e : x.testBit q = (x >>> q).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  rw [Nat.and_one_is_mod, e, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (x >>> q) with h | h <;> rw [h] <;> rfl

theorem shl_eq' (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

theorem div_eq' (a b : ℕ) : Nat.div a b = a / b := rfl

theorem mod_eq' (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem testBit_nIf (c : Bool) (x t : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) 0 x c).testBit t = (c && x.testBit t) := by
  cases c <;> simp

theorem pw2_pow (w : ℕ) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

public theorem kronK_eq_proved (rows : Array ℕ) : kronK rows = kron6K fun i => rows.getD i 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Bool.eq_iff_iff]
  unfold kron6K
  rw [testBit_orN_iff]
  simp only [shl_eq', div_eq', mod_eq', Nat.mul_eq, Nat.add_eq, Nat.testBit_shiftLeft,
    Bool.and_eq_true, decide_eq_true_eq, testBit_orN_iff, beq_bitN, testBit_nIf, pw2_pow,
    Nat.testBit_two_pow]
  rw [kronK, testBit_keyOf, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, h⟩
    have hr : p / 12 < 12 := by omega
    have e : (Array.ofFn (n := 12) fun r : Fin 12 =>
        bitsOf 12 fun q => (q % 2 == (r : ℕ) % 2) && (rows.getD ((r : ℕ) / 2) 0).testBit (q / 2)).getD
          (p / 12) 0 = bitsOf 12 fun q => (q % 2 == (p / 12) % 2) &&
            (rows.getD ((p / 12) / 2) 0).testBit (q / 2) := by
      simp [Array.getD_eq_getD_getElem?, hr]
    rw [e, testBit_bitsOf, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨-, h1, h2⟩ := h
    refine ⟨p / 12, hr, by omega, (p % 12) / 2, by omega, h2, by omega⟩
  · rintro ⟨r, hr, h1, q, hq, h2, h3⟩
    have hp : p < 144 := by omega
    have e1 : p / 12 = r := by omega
    have e2 : p % 12 = 2 * q + r % 2 := by omega
    refine ⟨hp, ?_⟩
    have e : (Array.ofFn (n := 12) fun r : Fin 12 =>
        bitsOf 12 fun q => (q % 2 == (r : ℕ) % 2) && (rows.getD ((r : ℕ) / 2) 0).testBit (q / 2)).getD
          (p / 12) 0 = bitsOf 12 fun q => (q % 2 == (p / 12) % 2) &&
            (rows.getD ((p / 12) / 2) 0).testBit (q / 2) := by
      simp [Array.getD_eq_getD_getElem?, show p / 12 < 12 by omega]
    rw [e, testBit_bitsOf, e1, e2]
    have e3 : (2 * q + r % 2) / 2 = q := by omega
    have e4 : (2 * q + r % 2) % 2 = r % 2 := by omega
    rw [Array.getD_eq_getD_getElem?] at h2
    simp [e3, e4, h2, show 2 * q + r % 2 < 12 by omega]

end CFSG.KC.O8
