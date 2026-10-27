module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem primaryPart_eq_power_of_coprime_factors {G : Type*} [Group G]
    {element primary regular : G} (hproduct : primary * regular = element)
    (hcommute : Commute primary regular)
    (hcoprime : Nat.Coprime (orderOf primary) (orderOf regular)) :
    ∃ exponent : ℕ, element ^ exponent = primary := by
  let exponent := Nat.chineseRemainder hcoprime 1 0
  refine ⟨exponent.val, ?_⟩
  rw [← hproduct, hcommute.mul_pow]
  have hprimary : primary ^ exponent.val = primary := by
    simpa using (pow_eq_pow_iff_modEq.mpr exponent.property.1 :
      primary ^ exponent.val = primary ^ 1)
  have hregular : regular ^ exponent.val = 1 := by
    simpa using (pow_eq_pow_iff_modEq.mpr exponent.property.2 :
      regular ^ exponent.val = regular ^ 0)
  simp [hprimary, hregular]

theorem primaryPart_eq_power {G : Type*} [Group G] {prime : ℕ}
    {element primary : G} (hprimary : BlocksIsPPart prime element primary) :
    ∃ exponent : ℕ, element ^ exponent = primary := by
  rcases hprimary with ⟨regular, hproduct, hproduct', ⟨power, horder⟩, hpositive, hcoprime⟩
  apply primaryPart_eq_power_of_coprime_factors hproduct
    (hproduct.trans hproduct'.symm)
  rw [horder]
  exact hcoprime.symm.pow_left power

@[expose] def twoSidedPermutation {G : Type*} [Group G] (left right : G) : Equiv.Perm G where
  toFun element := left * element * right⁻¹
  invFun element := left⁻¹ * element * right
  left_inv element := by simp [mul_assoc]
  right_inv element := by simp [mul_assoc]

@[simp] theorem twoSidedPermutation_apply {G : Type*} [Group G]
    (left right element : G) : twoSidedPermutation left right element = left * element * right⁻¹ :=
  rfl

@[simp] theorem twoSidedPermutation_one {G : Type*} [Group G] :
    twoSidedPermutation (1 : G) 1 = 1 := by
  ext element
  simp

theorem twoSidedPermutation_mul {G : Type*} [Group G]
    (left right left' right' : G) :
    twoSidedPermutation (left * left') (right * right') =
      twoSidedPermutation left right * twoSidedPermutation left' right' := by
  ext element
  simp [mul_assoc]

@[simp] theorem twoSidedPermutation_pow {G : Type*} [Group G]
    (left right : G) (exponent : ℕ) :
    twoSidedPermutation left right ^ exponent =
      twoSidedPermutation (left ^ exponent) (right ^ exponent) := by
  induction exponent with
  | zero => simp
  | succ exponent hInduction =>
    rw [pow_succ, hInduction, ← twoSidedPermutation_mul, ← pow_succ, ← pow_succ]

theorem primaryPart_twoSidedPermutation {G : Type*} [Group G]
    {prime : ℕ} (hprime : prime.Prime) {left right leftPrimary rightPrimary : G}
    (hleft : BlocksIsPPart prime left leftPrimary)
    (hright : BlocksIsPPart prime right rightPrimary) :
    BlocksIsPPart prime (twoSidedPermutation left right)
      (twoSidedPermutation leftPrimary rightPrimary) := by
  rcases hleft with ⟨leftRegular, hLeftProduct, hLeftProduct',
    ⟨leftPower, hLeftOrder⟩, hLeftPositive, hLeftCoprime⟩
  rcases hright with ⟨rightRegular, hRightProduct, hRightProduct',
    ⟨rightPower, hRightOrder⟩, hRightPositive, hRightCoprime⟩
  refine ⟨twoSidedPermutation leftRegular rightRegular, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← twoSidedPermutation_mul, hLeftProduct, hRightProduct]
  · rw [← twoSidedPermutation_mul, hLeftProduct', hRightProduct']
  · have hLeftDivides : orderOf leftPrimary ∣ prime ^ (leftPower + rightPower) := by
      rw [hLeftOrder, pow_add]
      exact dvd_mul_right _ _
    have hRightDivides : orderOf rightPrimary ∣ prime ^ (leftPower + rightPower) := by
      rw [hRightOrder, pow_add]
      exact dvd_mul_left _ _
    have hPower : twoSidedPermutation leftPrimary rightPrimary ^
        (prime ^ (leftPower + rightPower)) = 1 := by
      rw [twoSidedPermutation_pow, orderOf_dvd_iff_pow_eq_one.mp hLeftDivides,
        orderOf_dvd_iff_pow_eq_one.mp hRightDivides, twoSidedPermutation_one]
    have hOrderDivides := orderOf_dvd_iff_pow_eq_one.mpr hPower
    exact (Nat.dvd_prime_pow hprime).mp hOrderDivides |>.imp fun _ hOrder => hOrder.2
  · have hPower : twoSidedPermutation leftRegular rightRegular ^
        (orderOf leftRegular * orderOf rightRegular) = 1 := by
      rw [twoSidedPermutation_pow]
      rw [orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_right _ _),
        orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_left _ _), twoSidedPermutation_one]
    have hOrderDivides := orderOf_dvd_iff_pow_eq_one.mpr hPower
    exact Nat.pos_of_dvd_of_pos hOrderDivides (Nat.mul_pos hLeftPositive hRightPositive)
  · have hPower : twoSidedPermutation leftRegular rightRegular ^
        (orderOf leftRegular * orderOf rightRegular) = 1 := by
      rw [twoSidedPermutation_pow]
      rw [orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_right _ _),
        orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_left _ _), twoSidedPermutation_one]
    exact (hLeftCoprime.mul_left hRightCoprime).of_dvd_left
      (orderOf_dvd_iff_pow_eq_one.mpr hPower)

theorem twoSidedPermutation_no_fixedPoint {G : Type*} [Group G]
    {left right : G} (hnotConjugate : ¬ IsConj left right) (element : G) :
    twoSidedPermutation left right element ≠ element := by
  intro hfixed
  apply hnotConjugate
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨element, ?_⟩
  change left * element * right⁻¹ = element at hfixed
  have hEqual := congrArg (fun value => value * right * element⁻¹) hfixed
  simpa [mul_assoc] using hEqual.symm

end CFSG.BlockSectionOrthogonality.Helpers
