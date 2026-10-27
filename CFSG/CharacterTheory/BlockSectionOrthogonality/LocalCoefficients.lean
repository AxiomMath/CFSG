module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

theorem algebraicInteger_mem_localRing (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (integer : BlocksAlgInt) : (integer : ℂ) ∈ BlocksLocalRing m := by
  exact ⟨integer, 1, hm.isPrime.one_notMem, by simp⟩

theorem localRing_zero_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (0 : ℂ) ∈ BlocksLocalRing m := by
  simpa using algebraicInteger_mem_localRing m hm 0

theorem localRing_one_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (1 : ℂ) ∈ BlocksLocalRing m := by
  simpa using algebraicInteger_mem_localRing m hm 1

theorem localRing_add_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hleft : left ∈ BlocksLocalRing m)
    (hright : right ∈ BlocksLocalRing m) : left + right ∈ BlocksLocalRing m := by
  rcases hleft with ⟨numeratorLeft, denominatorLeft, hdenominatorLeft, rfl⟩
  rcases hright with ⟨numeratorRight, denominatorRight, hdenominatorRight, rfl⟩
  have hdenominator : denominatorLeft * denominatorRight ∉ m := by
    simpa only [hm.isPrime.mul_mem_iff_mem_or_mem, not_or] using
      And.intro hdenominatorLeft hdenominatorRight
  refine ⟨numeratorLeft * denominatorRight + numeratorRight * denominatorLeft,
    denominatorLeft * denominatorRight, hdenominator, ?_⟩
  have hleftZero : (denominatorLeft : ℂ) ≠ 0 := by
    intro hzero
    apply hdenominatorLeft
    have : denominatorLeft = 0 := Subtype.ext hzero
    simp [this]
  have hrightZero : (denominatorRight : ℂ) ≠ 0 := by
    intro hzero
    apply hdenominatorRight
    have : denominatorRight = 0 := Subtype.ext hzero
    simp [this]
  push_cast
  simpa only [mul_comm] using div_add_div (numeratorLeft : ℂ)
    (numeratorRight : ℂ) hleftZero hrightZero

theorem localRing_mul_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hleft : left ∈ BlocksLocalRing m)
    (hright : right ∈ BlocksLocalRing m) : left * right ∈ BlocksLocalRing m := by
  rcases hleft with ⟨numeratorLeft, denominatorLeft, hdenominatorLeft, rfl⟩
  rcases hright with ⟨numeratorRight, denominatorRight, hdenominatorRight, rfl⟩
  refine ⟨numeratorLeft * numeratorRight, denominatorLeft * denominatorRight, ?_, ?_⟩
  · simpa only [hm.isPrime.mul_mem_iff_mem_or_mem, not_or] using
      And.intro hdenominatorLeft hdenominatorRight
  · push_cast
    exact div_mul_div_comm _ _ _ _

theorem localRing_neg_mem (m : Ideal BlocksAlgInt)
    {value : ℂ} (hvalue : value ∈ BlocksLocalRing m) : -value ∈ BlocksLocalRing m := by
  rcases hvalue with ⟨numerator, denominator, hdenominator, rfl⟩
  exact ⟨-numerator, denominator, hdenominator, by simp [neg_div]⟩

@[expose] def localCoefficientSubring (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) : Subring ℂ where
  carrier := BlocksLocalRing m
  zero_mem' := localRing_zero_mem m hm
  one_mem' := localRing_one_mem m hm
  add_mem' := localRing_add_mem m hm
  mul_mem' := localRing_mul_mem m hm
  neg_mem' := localRing_neg_mem m

@[simp] theorem mem_localCoefficientSubring (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (value : ℂ) : value ∈ localCoefficientSubring m hm ↔ value ∈ BlocksLocalRing m :=
  Iff.rfl

theorem integral_mem_localRing (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {value : ℂ} (hvalue : IsIntegral ℤ value) : value ∈ BlocksLocalRing m := by
  exact algebraicInteger_mem_localRing m hm
    ⟨value, (mem_integralClosure_iff ℤ ℂ).mpr hvalue⟩

theorem algebraicInteger_coe_ne_zero_of_not_mem (m : Ideal BlocksAlgInt)
    {integer : BlocksAlgInt} (hinteger : integer ∉ m) : (integer : ℂ) ≠ 0 := by
  intro hzero
  apply hinteger
  have : integer = 0 := Subtype.ext hzero
  simp [this]

theorem localCoefficient_fraction_isUnit (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (numerator denominator : BlocksAlgInt) (hdenominator : denominator ∉ m)
    (hnumerator : numerator ∉ m) :
    IsUnit (⟨(numerator : ℂ) / (denominator : ℂ),
      ⟨numerator, denominator, hdenominator, rfl⟩⟩ : localCoefficientSubring m hm) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨(denominator : ℂ) / (numerator : ℂ),
    ⟨denominator, numerator, hnumerator, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change (numerator : ℂ) / (denominator : ℂ) *
    ((denominator : ℂ) / (numerator : ℂ)) = 1
  field_simp [algebraicInteger_coe_ne_zero_of_not_mem m hnumerator,
    algebraicInteger_coe_ne_zero_of_not_mem m hdenominator]

theorem localCoefficient_fraction_not_isUnit (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (numerator denominator : BlocksAlgInt) (hdenominator : denominator ∉ m)
    (hnumerator : numerator ∈ m) :
    ¬ IsUnit (⟨(numerator : ℂ) / (denominator : ℂ),
      ⟨numerator, denominator, hdenominator, rfl⟩⟩ : localCoefficientSubring m hm) := by
  intro hUnit
  obtain ⟨inverse, hInverse⟩ := isUnit_iff_exists_inv.mp hUnit
  rcases inverse.property with ⟨inverseNumerator, inverseDenominator, hInverseDenominator,
    hInverseValue⟩
  have hComplex := congrArg (fun value : localCoefficientSubring m hm => (value : ℂ)) hInverse
  change (numerator : ℂ) / (denominator : ℂ) * (inverse : ℂ) = 1 at hComplex
  rw [hInverseValue, div_mul_div_comm] at hComplex
  have hProduct : numerator * inverseNumerator = denominator * inverseDenominator := by
    apply Subtype.ext
    have hDenominator : (denominator : ℂ) * (inverseDenominator : ℂ) ≠ 0 :=
      mul_ne_zero (algebraicInteger_coe_ne_zero_of_not_mem m hdenominator)
        (algebraicInteger_coe_ne_zero_of_not_mem m hInverseDenominator)
    have hCross := (div_eq_iff hDenominator).mp hComplex
    simpa only [one_mul, Subalgebra.coe_mul] using hCross
  have hInIdeal : numerator * inverseNumerator ∈ m := m.mul_mem_right _ hnumerator
  rw [hProduct] at hInIdeal
  rcases hm.isPrime.mem_or_mem hInIdeal with hImpossible | hImpossible
  · exact hdenominator hImpossible
  · exact hInverseDenominator hImpossible

instance localCoefficient_isLocalRing (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    IsLocalRing (localCoefficientSubring m hm) := by
  classical
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro value
  rcases value.property with ⟨numerator, denominator, hdenominator, hValue⟩
  by_cases hnumerator : numerator ∈ m
  · right
    have hDifference : denominator - numerator ∉ m := by
      intro hInIdeal
      apply hdenominator
      have := m.add_mem hInIdeal hnumerator
      simpa using this
    have hUnit := localCoefficient_fraction_isUnit m hm (denominator - numerator)
      denominator hdenominator hDifference
    convert hUnit using 1
    apply Subtype.ext
    change 1 - (value : ℂ) = ((denominator - numerator : BlocksAlgInt) : ℂ) /
      (denominator : ℂ)
    rw [hValue]
    push_cast
    field_simp [algebraicInteger_coe_ne_zero_of_not_mem m hdenominator]
  · left
    have hUnit := localCoefficient_fraction_isUnit m hm numerator denominator
      hdenominator hnumerator
    convert hUnit using 1
    exact Subtype.ext hValue

theorem localCoefficient_natCast_not_isUnit (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprimeMem : (prime : BlocksAlgInt) ∈ m) :
    ¬ IsUnit (prime : localCoefficientSubring m hm) := by
  have hNotUnit := localCoefficient_fraction_not_isUnit m hm (prime : BlocksAlgInt) 1
    hm.isPrime.one_notMem hprimeMem
  have hEqual : (prime : localCoefficientSubring m hm) =
      ⟨((prime : BlocksAlgInt) : ℂ) / ((1 : BlocksAlgInt) : ℂ),
        ⟨(prime : BlocksAlgInt), 1, hm.isPrime.one_notMem, rfl⟩⟩ := by
    apply Subtype.ext
    simp
  rw [hEqual]
  exact hNotUnit

theorem localCoefficient_residue_charP (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : prime.Prime) (hprimeMem : (prime : BlocksAlgInt) ∈ m) :
    CharP (IsLocalRing.ResidueField (localCoefficientSubring m hm)) prime := by
  apply (CharP.charP_iff_prime_eq_zero hprime).mpr
  have hZero : IsLocalRing.residue (localCoefficientSubring m hm)
      (prime : localCoefficientSubring m hm) = 0 := by
    by_contra hNonzero
    exact localCoefficient_natCast_not_isUnit m hm prime hprimeMem
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hNonzero)
  simpa using hZero

theorem localCoefficient_root_residue_eq_one (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : prime.Prime) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (root : localCoefficientSubring m hm) (hroot : root ^ prime = 1) :
    IsLocalRing.residue (localCoefficientSubring m hm) root = 1 := by
  let := localCoefficient_residue_charP m hm prime hprime hprimeMem
  let : Fact prime.Prime := ⟨hprime⟩
  have hPower : (IsLocalRing.residue (localCoefficientSubring m hm) root - 1) ^ prime = 0 := by
    rw [sub_pow_char, ← map_pow, hroot, map_one, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff hprime.ne_zero).mp hPower)

end CFSG.BlockSectionOrthogonality.Helpers
