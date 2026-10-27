module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem one_not_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (1 : BlocksAlgInt) ∉ m := by
  exact fun hone => hm.ne_top (Ideal.eq_top_of_isUnit_mem m hone isUnit_one)

theorem denominator_ne_zero (m : Ideal BlocksAlgInt) {denominator : BlocksAlgInt}
    (hdenominator : denominator ∉ m) : (denominator : ℂ) ≠ 0 := by
  intro hzero
  apply hdenominator
  have : denominator = 0 := Subtype.ext hzero
  simpa only [this] using m.zero_mem

theorem localRing_of_algInt (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (value : BlocksAlgInt) : (value : ℂ) ∈ BlocksLocalRing m := by
  exact ⟨value, 1, one_not_mem m hm, by simp⟩

theorem localRing_zero (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (0 : ℂ) ∈ BlocksLocalRing m := by
  simpa using localRing_of_algInt m hm 0

theorem localRing_one (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (1 : ℂ) ∈ BlocksLocalRing m := by
  simpa using localRing_of_algInt m hm 1

theorem localRing_neg (m : Ideal BlocksAlgInt) {value : ℂ}
    (hvalue : value ∈ BlocksLocalRing m) : -value ∈ BlocksLocalRing m := by
  obtain ⟨numerator, denominator, hdenominator, rfl⟩ := hvalue
  exact ⟨-numerator, denominator, hdenominator, by simp [neg_div]⟩

theorem localRing_add (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : ℂ}
    (hleft : left ∈ BlocksLocalRing m) (hright : right ∈ BlocksLocalRing m) :
    left + right ∈ BlocksLocalRing m := by
  obtain ⟨numLeft, denLeft, hdenLeft, rfl⟩ := hleft
  obtain ⟨numRight, denRight, hdenRight, rfl⟩ := hright
  refine ⟨numLeft * denRight + numRight * denLeft, denLeft * denRight,
    fun hproduct => ?_, ?_⟩
  · exact (hm.isPrime.mem_or_mem hproduct).elim hdenLeft hdenRight
  · change (numLeft : ℂ) / denLeft + (numRight : ℂ) / denRight =
      ((numLeft : ℂ) * denRight + (numRight : ℂ) * denLeft) /
        ((denLeft : ℂ) * denRight)
    simpa only [mul_comm] using
      div_add_div (numLeft : ℂ) (numRight : ℂ)
        (denominator_ne_zero m hdenLeft) (denominator_ne_zero m hdenRight)

theorem localRing_mul (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : ℂ}
    (hleft : left ∈ BlocksLocalRing m) (hright : right ∈ BlocksLocalRing m) :
    left * right ∈ BlocksLocalRing m := by
  obtain ⟨numLeft, denLeft, hdenLeft, rfl⟩ := hleft
  obtain ⟨numRight, denRight, hdenRight, rfl⟩ := hright
  refine ⟨numLeft * numRight, denLeft * denRight, fun hproduct => ?_, ?_⟩
  · exact (hm.isPrime.mem_or_mem hproduct).elim hdenLeft hdenRight
  · change (numLeft : ℂ) / denLeft * ((numRight : ℂ) / denRight) =
      ((numLeft : ℂ) * numRight) / ((denLeft : ℂ) * denRight)
    exact div_mul_div_comm _ _ _ _

theorem localRing_sub (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : ℂ}
    (hleft : left ∈ BlocksLocalRing m) (hright : right ∈ BlocksLocalRing m) :
    left - right ∈ BlocksLocalRing m := by
  simpa only [sub_eq_add_neg] using localRing_add m hm hleft (localRing_neg m hright)

theorem localMaxIdeal_subset (m : Ideal BlocksAlgInt) :
    BlocksLocalMaxIdeal m ⊆ BlocksLocalRing m := by
  rintro value ⟨numerator, denominator, _, hdenominator, hvalue⟩
  exact ⟨numerator, denominator, hdenominator, hvalue⟩

theorem localMaxIdeal_of_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {value : BlocksAlgInt} (hvalue : value ∈ m) :
    (value : ℂ) ∈ BlocksLocalMaxIdeal m := by
  exact ⟨value, 1, hvalue, one_not_mem m hm, by simp⟩

theorem localMaxIdeal_zero (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (0 : ℂ) ∈ BlocksLocalMaxIdeal m := by
  simpa using localMaxIdeal_of_mem m hm m.zero_mem

theorem localMaxIdeal_neg (m : Ideal BlocksAlgInt) {value : ℂ}
    (hvalue : value ∈ BlocksLocalMaxIdeal m) : -value ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨numerator, denominator, hnumerator, hdenominator, rfl⟩ := hvalue
  exact ⟨-numerator, denominator, m.neg_mem hnumerator, hdenominator,
    by simp [neg_div]⟩

theorem localMaxIdeal_add (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : ℂ}
    (hleft : left ∈ BlocksLocalMaxIdeal m) (hright : right ∈ BlocksLocalMaxIdeal m) :
    left + right ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨numLeft, denLeft, hnumLeft, hdenLeft, rfl⟩ := hleft
  obtain ⟨numRight, denRight, hnumRight, hdenRight, rfl⟩ := hright
  refine ⟨numLeft * denRight + numRight * denLeft, denLeft * denRight,
    m.add_mem (m.mul_mem_right denRight hnumLeft) (m.mul_mem_right denLeft hnumRight),
    fun hproduct => ?_, ?_⟩
  · exact (hm.isPrime.mem_or_mem hproduct).elim hdenLeft hdenRight
  · change (numLeft : ℂ) / denLeft + (numRight : ℂ) / denRight =
      ((numLeft : ℂ) * denRight + (numRight : ℂ) * denLeft) /
        ((denLeft : ℂ) * denRight)
    simpa only [mul_comm] using
      div_add_div (numLeft : ℂ) (numRight : ℂ)
        (denominator_ne_zero m hdenLeft) (denominator_ne_zero m hdenRight)

theorem localMaxIdeal_sub (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : ℂ}
    (hleft : left ∈ BlocksLocalMaxIdeal m) (hright : right ∈ BlocksLocalMaxIdeal m) :
    left - right ∈ BlocksLocalMaxIdeal m := by
  simpa only [sub_eq_add_neg] using localMaxIdeal_add m hm hleft (localMaxIdeal_neg m hright)

theorem localMaxIdeal_mul_localRing (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hleft : left ∈ BlocksLocalMaxIdeal m)
    (hright : right ∈ BlocksLocalRing m) : left * right ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨numLeft, denLeft, hnumLeft, hdenLeft, rfl⟩ := hleft
  obtain ⟨numRight, denRight, hdenRight, rfl⟩ := hright
  refine ⟨numLeft * numRight, denLeft * denRight, m.mul_mem_right numRight hnumLeft,
    fun hproduct => ?_, ?_⟩
  · exact (hm.isPrime.mem_or_mem hproduct).elim hdenLeft hdenRight
  · change (numLeft : ℂ) / denLeft * ((numRight : ℂ) / denRight) =
      ((numLeft : ℂ) * numRight) / ((denLeft : ℂ) * denRight)
    exact div_mul_div_comm _ _ _ _

theorem localMaxIdeal_trans (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left middle right : ℂ} (hleft : left - middle ∈ BlocksLocalMaxIdeal m)
    (hright : middle - right ∈ BlocksLocalMaxIdeal m) :
    left - right ∈ BlocksLocalMaxIdeal m := by
  convert localMaxIdeal_add m hm hleft hright using 1
  ring

theorem localRing_sum (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {index : Type*}
    (indices : Finset index) (values : index → ℂ)
    (hvalues : ∀ entry ∈ indices, values entry ∈ BlocksLocalRing m) :
    (∑ entry ∈ indices, values entry) ∈ BlocksLocalRing m := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using localRing_zero m hm
  | @insert entry indices hentry hinduction =>
      rw [Finset.sum_insert hentry]
      exact localRing_add m hm (hvalues entry (Finset.mem_insert_self entry indices))
        (hinduction (fun other hother => hvalues other (Finset.mem_insert_of_mem hother)))

theorem localMaxIdeal_sum (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {index : Type*}
    (indices : Finset index) (values : index → ℂ)
    (hvalues : ∀ entry ∈ indices, values entry ∈ BlocksLocalMaxIdeal m) :
    (∑ entry ∈ indices, values entry) ∈ BlocksLocalMaxIdeal m := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using localMaxIdeal_zero m hm
  | @insert entry indices hentry hinduction =>
      rw [Finset.sum_insert hentry]
      exact localMaxIdeal_add m hm (hvalues entry (Finset.mem_insert_self entry indices))
        (hinduction (fun other hother => hvalues other (Finset.mem_insert_of_mem hother)))

theorem localMaxIdeal_intCast_of_dvd (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : (prime : BlocksAlgInt) ∈ m) {integer : ℤ}
    (hdivides : (prime : ℤ) ∣ integer) : (integer : ℂ) ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨factor, rfl⟩ := hdivides
  have hproduct : ((prime : ℤ) * factor : BlocksAlgInt) ∈ m := by
    simpa only [Int.cast_mul, Int.cast_natCast] using m.mul_mem_right (factor : BlocksAlgInt) hprime
  simpa using localMaxIdeal_of_mem m hm hproduct

theorem localMaxIdeal_natCard_difference (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : (prime : BlocksAlgInt) ∈ m) {left right : ℕ}
    (hcongruent : left ≡ right [MOD prime]) :
    (left : ℂ) - right ∈ BlocksLocalMaxIdeal m := by
  have hdivides : (prime : ℤ) ∣ (left : ℤ) - right := hcongruent.symm.dvd
  simpa only [Int.cast_sub, Int.cast_natCast] using
    localMaxIdeal_intCast_of_dvd m hm prime hprime hdivides

theorem common_denominator (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {index : Type*}
    (indices : Finset index) (values : index → ℂ)
    (hvalues : ∀ entry ∈ indices, values entry ∈ BlocksLocalRing m) :
    ∃ denominator : BlocksAlgInt, denominator ∉ m ∧
      ∀ entry ∈ indices, ∃ numerator : BlocksAlgInt,
        (numerator : ℂ) = (denominator : ℂ) * values entry := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨1, one_not_mem m hm, by simp⟩
  | @insert entry indices hentry hinduction =>
      obtain ⟨oldDenominator, holdDenominator, holdValues⟩ :=
        hinduction (fun other hother => hvalues other (Finset.mem_insert_of_mem hother))
      obtain ⟨newNumerator, newDenominator, hnewDenominator, hnewValue⟩ :=
        hvalues entry (Finset.mem_insert_self entry indices)
      refine ⟨oldDenominator * newDenominator,
        fun hproduct => (hm.isPrime.mem_or_mem hproduct).elim holdDenominator hnewDenominator,
        ?_⟩
      intro other hother
      obtain rfl | hother := Finset.mem_insert.mp hother
      · refine ⟨oldDenominator * newNumerator, ?_⟩
        change (oldDenominator : ℂ) * newNumerator =
          ((oldDenominator : ℂ) * newDenominator) * values other
        rw [hnewValue]
        field_simp [denominator_ne_zero m hnewDenominator]
      · obtain ⟨oldNumerator, hcoefficient⟩ := holdValues other hother
        refine ⟨newDenominator * oldNumerator, ?_⟩
        change (newDenominator : ℂ) * oldNumerator =
          ((oldDenominator : ℂ) * newDenominator) * values other
        rw [hcoefficient]
        ring

end CFSG.BrauerThirdMainTheorem.Helpers
