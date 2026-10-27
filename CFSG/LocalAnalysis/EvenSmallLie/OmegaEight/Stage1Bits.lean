module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev V6 := Fin 6 → ZMod 2

@[expose] def vecBits (v : V6) : ℕ := bitsOf 6 fun i => if h : i < 6 then v ⟨i, h⟩ == 1 else false

theorem testBit_vecBits (v : V6) (i : ℕ) :
    (vecBits v).testBit i = if h : i < 6 then v ⟨i, h⟩ == 1 else false := by
  rw [vecBits, testBit_bitsOf]
  by_cases h : i < 6 <;> simp [h]

theorem toVec_vecBits (v : V6) : toVec 6 (vecBits v) = v := by
  ext i
  rw [toVec, testBit_vecBits, dite_eq_left i.isLt, bz_beq_one]

theorem vecBits_lt (v : V6) : vecBits v < 64 := by
  refine Nat.lt_pow_two_of_testBit (n := 6) _ fun i hi => ?_
  rw [testBit_vecBits, dite_eq_right (by omega)]

theorem vecBits_toVec {x : ℕ} (hx : x < 64) : vecBits (toVec 6 x) = x := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_vecBits]
  by_cases h : i < 6
  · rw [dite_eq_left h, toVec]
    cases x.testBit i <;> rfl
  · have h64 : 64 ≤ 2 ^ i :=
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [dite_eq_right h, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h64)]

theorem toVec_injective {x y : ℕ} (hx : x < 64) (hy : y < 64) (h : toVec 6 x = toVec 6 y) :
    x = y := by
  rw [← vecBits_toVec hx, ← vecBits_toVec hy, h]

theorem vecBits_add (v w : V6) : vecBits (v + w) = vecBits v ^^^ vecBits w := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_xor, testBit_vecBits, testBit_vecBits, testBit_vecBits]
  by_cases h : i < 6
  · simp only [dite_eq_left h, Pi.add_apply]
    generalize v ⟨i, h⟩ = a
    generalize w ⟨i, h⟩ = b
    fin_cases a <;> fin_cases b <;> rfl
  · simp [dite_eq_right h]

theorem vecBits_zero : vecBits 0 = 0 := by
  rw [← vecBits_toVec (x := 0) (by norm_num)]
  congr 1
  ext i
  simp [toVec]

theorem toVec_xor (x y : ℕ) : toVec 6 (x ^^^ y) = toVec 6 x + toVec 6 y := by
  ext i
  simp [toVec, Nat.testBit_xor, bz_xor]

theorem toVec_two_pow' (j : Fin 6) : toVec 6 (2 ^ (j : ℕ)) = Pi.single j 1 := by
  ext i
  rw [toVec, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]
    have : (j : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
    simp [this]

@[expose] def qfV (ε : Eps) (v : V6) : ZMod 2 := bz (qfB ε (vecBits v))

@[expose] def genMat (ε : Eps) (i : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) := toMat 6 6 (genRows ε i)

@[expose] def genInvMat (ε : Eps) (i : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  toMat 6 6 (genInvRows ε i)

theorem mulVec_toVec (A : Array ℕ) (x : ℕ) :
    toMat 6 6 A *ᵥ toVec 6 x = toVec 6 (bmulVec 6 6 A x) :=
  (toVec_bmulVec 6 6 A x).symm

theorem bmulVec_lt (A : Array ℕ) (x : ℕ) : bmulVec 6 6 A x < 64 := by
  refine Nat.lt_pow_two_of_testBit (n := 6) _ fun i hi => ?_
  rw [bmulVec, testBit_bitsOf]
  simp [show ¬ i < 6 by omega]

theorem vecBits_mulVec (A : Array ℕ) (v : V6) :
    vecBits (toMat 6 6 A *ᵥ v) = bmulVec 6 6 A (vecBits v) := by
  conv_lhs => rw [← toVec_vecBits v]
  rw [mulVec_toVec, vecBits_toVec (bmulVec_lt _ _)]

theorem qfV_toVec (ε : Eps) {x : ℕ} (hx : x < 64) : qfV ε (toVec 6 x) = bz (qfB ε x) := by
  rw [qfV, vecBits_toVec hx]

theorem card_filter_vecBits (f : ℕ → Bool) :
    (Finset.univ.filter fun v : V6 => f (vecBits v) = true).card =
      ((Finset.range 64).filter fun x => f x = true).card := by
  apply Finset.card_bij (fun v _ => vecBits v)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv ⊢
    exact ⟨vecBits_lt v, hv⟩
  · intro v _ w _ h
    rw [← toVec_vecBits v, h, toVec_vecBits]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact ⟨toVec 6 x, by simpa [vecBits_toVec hx.1] using hx.2, vecBits_toVec hx.1⟩

@[expose] def nCount : Eps → ℕ
  | .plus => 28
  | .minus => 36

theorem qfV_eq_one_iff (ε : Eps) (v : V6) : qfV ε v = 1 ↔ qfB ε (vecBits v) = true := by
  rw [qfV]
  cases qfB ε (vecBits v) <;> simp [bz]

theorem qfV_eq_zero_iff (ε : Eps) (v : V6) : qfV ε v = 0 ↔ qfB ε (vecBits v) = false := by
  rw [qfV]
  cases qfB ε (vecBits v) <;> simp [bz]

theorem qfV_cases (ε : Eps) (v : V6) : qfV ε v = 0 ∨ qfV ε v = 1 := by
  rw [qfV]
  cases qfB ε (vecBits v) <;> simp [bz]

theorem card_qfV_one (ε : Eps) :
    (Finset.univ.filter fun v : V6 => qfV ε v = 1).card = nCount ε := by
  have h := card_filter_vecBits (qfB ε)
  simp only [← qfV_eq_one_iff] at h
  rw [h]
  cases ε <;> decide

theorem prime_one_add_nCount (ε : Eps) : (1 + nCount ε).Prime := by
  cases ε <;> norm_num [nCount]

theorem not_modEq_one_add_nCount (ε : Eps) {d : ℕ} (hd : d ∣ 128) (hd' : d < 128) :
    ¬ 128 ≡ d [MOD 1 + nCount ε] := by
  have hd2 : d ∈ Nat.divisors 128 := Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have : Nat.divisors 128 = {1, 2, 4, 8, 16, 32, 64, 128} := by decide
  rw [this] at hd2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd2
  rcases hd2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | omega | (cases ε <;> decide)

theorem qfV_zero (ε : Eps) : qfV ε 0 = 0 := by
  rw [qfV, vecBits_zero]
  cases ε <;> rfl

end CFSG.EvenSmallLie.OmegaEight.Stage1
