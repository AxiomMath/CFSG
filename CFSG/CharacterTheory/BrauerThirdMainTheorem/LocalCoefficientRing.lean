module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] def localCoefficientSubring (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) : Subring ℂ where
  carrier := BlocksLocalRing m
  zero_mem' := localRing_zero m hm
  one_mem' := localRing_one m hm
  add_mem' := localRing_add m hm
  mul_mem' := localRing_mul m hm
  neg_mem' := localRing_neg m

theorem localMaxIdeal_one_not (m : Ideal BlocksAlgInt) : (1 : ℂ) ∉ BlocksLocalMaxIdeal m := by
  rintro ⟨numerator, denominator, hnumerator, hdenominator, hequal⟩
  have hnonzero := denominator_ne_zero m hdenominator
  have hcast : (denominator : ℂ) = numerator := by
    simpa only [one_mul] using (eq_div_iff hnonzero).mp hequal
  have hequalInt : denominator = numerator := Subtype.ext hcast
  exact hdenominator (hequalInt ▸ hnumerator)

theorem localMaxIdeal_algInt_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (value : BlocksAlgInt) : (value : ℂ) ∈ BlocksLocalMaxIdeal m ↔ value ∈ m := by
  constructor
  · rintro ⟨numerator, denominator, hnumerator, hdenominator, hequal⟩
    have hcast : (value : ℂ) * denominator = numerator :=
      (eq_div_iff (denominator_ne_zero m hdenominator)).mp hequal
    have hequalInt : value * denominator = numerator := Subtype.ext hcast
    have hproduct : value * denominator ∈ m := hequalInt ▸ hnumerator
    exact (hm.isPrime.mem_or_mem hproduct).resolve_right hdenominator
  · exact localMaxIdeal_of_mem m hm

theorem localRing_inv_of_not_mem (m : Ideal BlocksAlgInt) {value : ℂ}
    (hvalue : value ∈ BlocksLocalRing m) (hnotMem : value ∉ BlocksLocalMaxIdeal m) :
    value⁻¹ ∈ BlocksLocalRing m := by
  obtain ⟨numerator, denominator, hdenominator, rfl⟩ := hvalue
  have hnumerator : numerator ∉ m := by
    intro hnumerator
    exact hnotMem ⟨numerator, denominator, hnumerator, hdenominator, rfl⟩
  exact ⟨denominator, numerator, hnumerator, inv_div _ _⟩

theorem localRing_isUnit_of_not_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (value : localCoefficientSubring m hm) (hvalue : (value : ℂ) ∉ BlocksLocalMaxIdeal m) :
    IsUnit value := by
  have hnonzero : (value : ℂ) ≠ 0 := by
    intro hzero
    exact hvalue (hzero ▸ localMaxIdeal_zero m hm)
  let inverse : localCoefficientSubring m hm :=
    ⟨(value : ℂ)⁻¹, localRing_inv_of_not_mem m value.property hvalue⟩
  exact ⟨⟨value, inverse, Subtype.ext (mul_inv_cancel₀ hnonzero),
    Subtype.ext (inv_mul_cancel₀ hnonzero)⟩, rfl⟩

@[expose] def localCoefficientMaxIdeal (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    Ideal (localCoefficientSubring m hm) where
  carrier := {value | (value : ℂ) ∈ BlocksLocalMaxIdeal m}
  zero_mem' := localMaxIdeal_zero m hm
  add_mem' := localMaxIdeal_add m hm
  smul_mem' := by
    intro scalar value hvalue
    change (scalar : ℂ) * (value : ℂ) ∈ BlocksLocalMaxIdeal m
    rw [mul_comm]
    exact localMaxIdeal_mul_localRing m hm hvalue scalar.property

theorem localCoefficientMaxIdeal_isMaximal (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    (localCoefficientMaxIdeal m hm).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨localMaxIdeal_one_not m, ?_⟩
  intro larger value _ hnotMember hmember
  have hunit := localRing_isUnit_of_not_mem m hm value hnotMember
  rw [larger.eq_top_of_isUnit_mem hmember hunit]
  exact Submodule.mem_top

@[expose] noncomputable def localResidueField (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :=
  localCoefficientSubring m hm ⧸ localCoefficientMaxIdeal m hm

noncomputable instance localResidueField_field (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    Field (localResidueField m hm) := by
  letI : (localCoefficientMaxIdeal m hm).IsMaximal := localCoefficientMaxIdeal_isMaximal m hm
  exact Ideal.Quotient.field _

@[expose] noncomputable def localResidue (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    localCoefficientSubring m hm →+* localResidueField m hm :=
  Ideal.Quotient.mk _

noncomputable instance localResidueField_algebra (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    Algebra (localCoefficientSubring m hm) (localResidueField m hm) := by
  unfold localResidueField
  infer_instance

theorem localResidue_algebraMap (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    algebraMap (localCoefficientSubring m hm) (localResidueField m hm) = localResidue m hm := rfl

theorem localResidue_eq_zero_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (value : localCoefficientSubring m hm) :
    localResidue m hm value = 0 ↔ (value : ℂ) ∈ BlocksLocalMaxIdeal m :=
  Ideal.Quotient.eq_zero_iff_mem

theorem localResidue_eq_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (left right : localCoefficientSubring m hm) :
    localResidue m hm left = localResidue m hm right ↔
      (left : ℂ) - right ∈ BlocksLocalMaxIdeal m := by
  rw [← sub_eq_zero, ← map_sub, localResidue_eq_zero_iff]
  rfl

theorem localResidueField_charP (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : prime.Prime) (hprimeMem : (prime : BlocksAlgInt) ∈ m) :
    CharP (localResidueField m hm) prime := by
  apply (CharP.charP_iff_prime_eq_zero hprime).mpr
  rw [← map_natCast (localResidue m hm), localResidue_eq_zero_iff]
  exact localMaxIdeal_of_mem m hm hprimeMem

end CFSG.BrauerThirdMainTheorem.Helpers
