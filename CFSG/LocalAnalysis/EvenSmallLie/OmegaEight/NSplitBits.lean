module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem toVec_xorN (n a b : ℕ) : toVec n (a ^^^ b) = toVec n a + toVec n b := by
  ext j
  simp only [toVec, Nat.testBit_xor, bz_xor, Pi.add_apply]

theorem toVec_zero (n : ℕ) : toVec n 0 = 0 := by
  ext j
  simp [toVec, bz]

@[expose] def foldOr (k n : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range k).foldl (fun acc g => acc ||| (f g <<< (n * g))) 0

theorem foldOr_succ (k n : ℕ) (f : ℕ → ℕ) :
    foldOr (k + 1) n f = foldOr k n f ||| (f k <<< (n * k)) := by
  rw [foldOr, List.range_succ, List.foldl_append]
  rfl

theorem testBit_foldOr {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) :
    ∀ k, (∀ g < k, f g < 2 ^ n) →
      ∀ j, (foldOr k n f).testBit j = (decide (j < n * k) && (f (j / n)).testBit (j % n)) := by
  intro k
  induction k with
  | zero => intro _ j; simp [foldOr]
  | succ k ih =>
    intro hf j
    rw [foldOr_succ, Nat.testBit_or, ih (fun g hg => hf g (by omega)), Nat.testBit_shiftLeft]
    by_cases hj : j < n * k
    · have h1 : ¬ (j ≥ n * k) := by omega
      have h2 : j < n * (k + 1) := by rw [Nat.mul_succ]; omega
      simp [hj, h1, h2]
    · simp only [hj, decide_false, Bool.false_and, Bool.false_or, ge_iff_le]
      by_cases hj' : j < n * (k + 1)
      · have hdiv : j / n = k := by
          apply Nat.div_eq_of_lt_le
          · rw [Nat.mul_comm]; omega
          · rw [Nat.succ_mul, Nat.mul_comm]; rw [Nat.mul_succ] at hj'; omega
        have hmod : j % n = j - n * k := by
          have := Nat.div_add_mod j n
          rw [hdiv] at this
          omega
        simp only [hj', decide_true, Bool.true_and, hdiv, hmod]
        have : n * k ≤ j := by omega
        simp [this]
      · simp only [hj', decide_false, Bool.false_and]
        have hge : j - n * k ≥ n := by rw [Nat.mul_succ] at hj'; omega
        have : (f k).testBit (j - n * k) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf k (by omega))
            (Nat.pow_le_pow_right (by norm_num) hge))
        simp [this]

@[expose] def blkN (n y g : ℕ) : ℕ := (y >>> (n * g)) % 2 ^ n

theorem blkN_lt (n y g : ℕ) : blkN n y g < 2 ^ n := Nat.mod_lt _ (by positivity)

theorem testBit_blkN (n y g b : ℕ) :
    (blkN n y g).testBit b = (decide (b < n) && y.testBit (n * g + b)) := by
  rw [blkN, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

@[expose] def unpackV (k n : ℕ) (y : Fin (k * n) → ZMod 2) : Fin k → Fin n → ZMod 2 :=
  fun g b => y (finProdFinEquiv (g, b))

@[expose] def packV (k n : ℕ) (F : Fin k → Fin n → ZMod 2) : Fin (k * n) → ZMod 2 :=
  fun i => F (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem unpackV_packV (k n : ℕ) (F : Fin k → Fin n → ZMod 2) : unpackV k n (packV k n F) = F := by
  ext g b
  simp [unpackV, packV]

theorem packV_unpackV (k n : ℕ) (y : Fin (k * n) → ZMod 2) : packV k n (unpackV k n y) = y := by
  ext i
  show y (finProdFinEquiv (finProdFinEquiv.symm i)) = y i
  rw [Equiv.apply_symm_apply]

theorem finProdFinEquiv_val {k n : ℕ} (g : Fin k) (b : Fin n) :
    ((finProdFinEquiv (g, b) : Fin (k * n)) : ℕ) = n * g + b := by
  rw [finProdFinEquiv_apply_val]
  ring

theorem toVec_foldOr {k n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) (hf : ∀ g < k, f g < 2 ^ n) :
    unpackV k n (toVec (k * n) (foldOr k n f)) = fun g : Fin k => toVec n (f g) := by
  ext g b
  simp only [unpackV, toVec, testBit_foldOr hn f k hf, finProdFinEquiv_val]
  have hb : (n * g + b) / n = g := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < n), Nat.div_eq_of_lt b.2,
      Nat.zero_add]
  have hb' : (n * g + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
  have hlt : n * g + b < n * k := by
    have := g.2
    nlinarith [b.2]
  simp [hb, hb', hlt]

theorem toVec_blkN {k n : ℕ} (y : ℕ) (g : Fin k) :
    toVec n (blkN n y g) = unpackV k n (toVec (k * n) y) g := by
  ext b
  simp only [toVec, testBit_blkN, b.2, decide_true, Bool.true_and, unpackV, finProdFinEquiv_val]

theorem foldOr_lt {k n : ℕ} (hn : 0 < n) (f : ℕ → ℕ) (hf : ∀ g < k, f g < 2 ^ n) :
    foldOr k n f < 2 ^ (n * k) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_foldOr hn f k hf]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hj

theorem packV_add (k n : ℕ) (F G : Fin k → Fin n → ZMod 2) :
    packV k n (F + G) = packV k n F + packV k n G := rfl

theorem unpackV_injective (k n : ℕ) : Function.Injective (unpackV k n) := fun y z h => by
  rw [← packV_unpackV k n y, h, packV_unpackV]

theorem bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> simp_all [bz]

theorem toVec_injective_lt {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : toVec n x = toVec n y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact bz_injective (congrFun h ⟨j, hj⟩)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (not_lt.1 hj))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right
      (by norm_num) (not_lt.1 hj)))]

@[expose] def bitsV (n : ℕ) (x : Fin n → ZMod 2) : ℕ :=
  bitsOf n fun i => if h : i < n then x ⟨i, h⟩ == 1 else false

theorem testBit_bitsV (n : ℕ) (x : Fin n → ZMod 2) (i : ℕ) :
    (bitsV n x).testBit i = if h : i < n then x ⟨i, h⟩ == 1 else false := by
  rw [bitsV, testBit_bitsOf]
  by_cases h : i < n <;> simp [h]

theorem toVec_bitsV (n : ℕ) (x : Fin n → ZMod 2) : toVec n (bitsV n x) = x := by
  ext i
  rw [toVec, testBit_bitsV, dite_eq_left i.isLt, bz_beq_one]

theorem bitsV_lt (n : ℕ) (x : Fin n → ZMod 2) : bitsV n x < 2 ^ n := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_bitsV, dite_eq_right (by omega)]

end CFSG.EvenSmallLie.OmegaEight.NSplit
