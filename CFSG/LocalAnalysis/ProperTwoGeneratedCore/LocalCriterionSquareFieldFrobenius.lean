module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic
public import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

variable {F : Type u} [Field F] [Finite F]

def binaryFrobenius [Algebra (ZMod 2) F] : F ≃ₐ[ZMod 2] F :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F

theorem binaryFrobenius_pow_apply [Algebra (ZMod 2) F] (s : ℕ) (c : F) :
    (binaryFrobenius (F := F) ^ s) c = c ^ (2 ^ s) := by
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ s) c = _
  rw [AlgEquiv.coe_pow]
  simpa using congrFun
    (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod 2) F s) c

theorem binary_degree_of_card [Algebra (ZMod 2) F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) : Module.finrank (ZMod 2) F = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hcard

theorem ringAut_card_and_cyclic {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    Nat.card (RingAut F) = n ∧ IsCyclic (RingAut F) := by
  let : CharP F 2 := char_two_of_card hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  refine ⟨?_, finite_field_ringAut_isCyclic 2⟩
  calc
    Nat.card (RingAut F) = Nat.card (F ≃ₐ[ZMod 2] F) :=
      Nat.card_congr (ringAutPrimeEquiv (F := F) 2).toEquiv
    _ = Module.finrank (ZMod 2) F :=
      Nat.card_congr (Equiv.ofBijective _
        (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F)).symm |>.trans
        (by simp)
    _ = n := binary_degree_of_card hcard

theorem finite_field_involution_exact {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧ (∀ c : F, sigma c = c ^ (2 ^ s)) ∧
      Nat.card (fixedField sigma) = 2 ^ s := by
  obtain ⟨s, hs, hns, hk⟩ := finite_field_involution_degree_and_fixed_card hn hcard
    sigma hsigma hne
  let : CharP F 2 := char_two_of_card hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let g := binaryFrobenius (F := F)
  have hgorder : orderOf g = n :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F).trans
      (binary_degree_of_card hcard)
  have hhalf : orderOf (g ^ s) = 2 := by
    have hdvd : s ∣ orderOf g := by rw [hgorder, hns]; exact dvd_mul_left s 2
    rw [orderOf_pow_of_dvd (by omega : s ≠ 0) hdvd, hgorder, hns]
    exact Nat.mul_div_cancel 2 (by omega : 0 < s)
  have horder : orderOf ((ringAutPrimeEquiv (F := F) 2) sigma) = 2 :=
    ((ringAutPrimeEquiv (F := F) 2).orderOf_eq sigma).trans (orderOf_eq_prime hsigma hne)
  have heq := cyclic_involutions_eq ((ringAutPrimeEquiv (F := F) 2) sigma) (g ^ s)
    horder hhalf
  refine ⟨s, hs, hns, ?_, hk⟩
  intro c
  have hc := DFunLike.congr_fun heq c
  exact hc.trans (binaryFrobenius_pow_apply s c)

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
