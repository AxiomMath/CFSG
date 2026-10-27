module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuadraticRatio
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.TwoRankLowerBound.Helpers

theorem two_quadratic_relations_force_values_eq_degrees {field : Type*} [Field field]
    (firstDegree secondDegree thirdDegree fourthDegree fifthDegree : field)
    (firstValue secondValue thirdValue fourthValue fifthValue : field)
    (hfirst : firstDegree ≠ 0) (hsecond : secondDegree ≠ 0) (hthird : thirdDegree ≠ 0)
    (hfourth : fourthDegree ≠ 0) (hfifth : fifthDegree ≠ 0)
    (hdegreefourth : fourthDegree = -secondDegree - thirdDegree)
    (hdegreefifth : fifthDegree = -firstDegree - thirdDegree)
    (hvaluefourth : fourthValue = secondValue + thirdValue)
    (hvaluefifth : fifthValue = firstValue + thirdValue)
    (hquadraticfourth : secondValue ^ 2 / secondDegree + thirdValue ^ 2 / thirdDegree +
      fourthValue ^ 2 / fourthDegree = 0)
    (hquadraticfifth : firstValue ^ 2 / firstDegree + thirdValue ^ 2 / thirdDegree +
      fifthValue ^ 2 / fifthDegree = 0)
    (hdegreesum : 1 + firstDegree + secondDegree + thirdDegree = 0)
    (hvaluesum : 1 + firstValue + secondValue + thirdValue = 0) :
    firstValue = firstDegree ∧ secondValue = secondDegree ∧ thirdValue = thirdDegree := by
  have hsecondratio := three_term_quadratic_ratio secondDegree thirdDegree fourthDegree
    secondValue thirdValue fourthValue hsecond hthird hfourth hdegreefourth hvaluefourth
    hquadraticfourth
  have hfirstratio := three_term_quadratic_ratio firstDegree thirdDegree fifthDegree
    firstValue thirdValue fifthValue hfirst hthird hfifth hdegreefifth hvaluefifth
    hquadraticfifth
  let ratio := thirdValue / thirdDegree
  have hfirstvalue : firstValue = ratio * firstDegree := by
    change firstValue = (thirdValue / thirdDegree) * firstDegree
    rw [← hfirstratio, div_mul_cancel₀ _ hfirst]
  have hsecondvalue : secondValue = ratio * secondDegree := by
    change secondValue = (thirdValue / thirdDegree) * secondDegree
    rw [← hsecondratio, div_mul_cancel₀ _ hsecond]
  have hthirdvalue : thirdValue = ratio * thirdDegree := by
    exact (div_mul_cancel₀ _ hthird).symm
  have hratioone : ratio = 1 := by
    rw [hfirstvalue, hsecondvalue, hthirdvalue] at hvaluesum
    linear_combination ratio * hdegreesum - hvaluesum
  simp only [hratioone, one_mul] at hfirstvalue hsecondvalue hthirdvalue
  exact ⟨hfirstvalue, hsecondvalue, hthirdvalue⟩

theorem three_character_quadratic_rigidity {field : Type*} [Field field]
    (leftDegree rightDegree leftValue rightValue : field)
    (hleft : leftDegree ≠ 0) (hright : rightDegree ≠ 0)
    (hdegrees : 1 + leftDegree + rightDegree = 0)
    (hvalues : 1 + leftValue + rightValue = 0)
    (hquadratic : 1 + leftValue ^ 2 / leftDegree + rightValue ^ 2 / rightDegree = 0) :
    leftValue = leftDegree ∧ rightValue = rightDegree := by
  have hrightdegree : rightDegree = -(1 : field) - leftDegree := by linear_combination hdegrees
  have hrightvalue : -rightValue = 1 + leftValue := by linear_combination -hvalues
  have hquadratic' : (1 : field) ^ 2 / 1 + leftValue ^ 2 / leftDegree +
      (-rightValue) ^ 2 / rightDegree = 0 := by simpa using hquadratic
  have hratio := three_term_quadratic_ratio (1 : field) leftDegree rightDegree 1 leftValue
    (-rightValue) one_ne_zero hleft hright hrightdegree hrightvalue hquadratic'
  have hleftvalue : leftValue = leftDegree := by
    have hratio' : leftValue / leftDegree = 1 := by simpa using hratio.symm
    exact (div_eq_one_iff_eq hleft).mp hratio'
  refine ⟨hleftvalue, ?_⟩
  rw [hleftvalue] at hvalues
  linear_combination hvalues - hdegrees

end CFSG.TwoRankLowerBound.Helpers
