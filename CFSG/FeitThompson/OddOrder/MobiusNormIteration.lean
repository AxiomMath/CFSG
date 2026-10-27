module

public import Mathlib.RingTheory.Norm.Defs
public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree
import CFSG.FeitThompson.OddOrder.SmallNormIndexLowerBound
import CFSG.FeitThompson.OddOrder.GeometricSumCongruences

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

variable {F : Type*} [Field F] {m : ℕ}

theorem two_sub_mem_normOneShiftSet {z : F} (hz : z ∈ normOneShiftSet F m) :
    2 - z ∈ normOneShiftSet F m := by
  rw [mem_normOneShiftSet] at hz ⊢
  exact ⟨hz.2, by rw [sub_sub_cancel]; exact hz.1⟩

theorem mapsTo_two_sub_normOneShiftSet :
    Set.MapsTo (fun z : F => 2 - z) (normOneShiftSet F m) (normOneShiftSet F m) :=
  fun _ hz => two_sub_mem_normOneShiftSet hz

def mobiusSeq (a : F) (k : ℕ) : F := 1 + k * (1 - a)

theorem mobiusSeq_apply (a : F) (k : ℕ) : mobiusSeq a k = 1 + k * (1 - a) := (rfl)

@[simp] theorem mobiusSeq_zero (a : F) : mobiusSeq a 0 = 1 := by simp [mobiusSeq_apply]

@[simp] theorem mobiusSeq_one (a : F) : mobiusSeq a 1 = 2 - a := by
  rw [mobiusSeq_apply]; push_cast; ring

theorem mobiusSeq_succ (a : F) (k : ℕ) : mobiusSeq a (k + 1) = mobiusSeq a k + (1 - a) := by
  simp only [mobiusSeq_apply]; push_cast; ring

theorem mobiusSeq_add_two (a : F) (k : ℕ) :
    mobiusSeq a (k + 2) = 2 * mobiusSeq a (k + 1) - mobiusSeq a k := by
  simp only [mobiusSeq_apply]; push_cast; ring

theorem mobiusSeq_spec (hm : m ≠ 0)
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) :
    mobiusSeq a k ≠ 0 ∧ mobiusSeq a k ^ m = 1 ∧
      mobiusSeq a k / mobiusSeq a (k + 1) ∈ normOneShiftSet F m := by
  induction k with
  | zero =>
    refine ⟨by simp, by simp, ?_⟩
    rw [mobiusSeq_zero, mobiusSeq_one, one_div]
    exact hinv _ (two_sub_mem_normOneShiftSet ha)
  | succ k ih =>
    obtain ⟨-, hkm, hkr⟩ := ih
    have hkr' := (mem_normOneShiftSet).1 hkr
    have hr0 : mobiusSeq a k / mobiusSeq a (k + 1) ≠ 0 :=
      ne_zero_of_mem_normOneShiftSet hm hkr
    have hk10 : mobiusSeq a (k + 1) ≠ 0 := by
      intro h; rw [h, div_zero] at hr0; exact hr0 rfl
    refine ⟨hk10, ?_, ?_⟩
    ·
      have h1 : mobiusSeq a k ^ m / mobiusSeq a (k + 1) ^ m = 1 := by
        rw [← div_pow]; exact hkr'.1
      rw [← (div_eq_one_iff_eq (pow_ne_zero _ hk10)).1 h1]
      exact hkm
    ·
      have hsub : 2 - mobiusSeq a k / mobiusSeq a (k + 1)
          = mobiusSeq a (k + 2) / mobiusSeq a (k + 1) := by
        rw [mobiusSeq_add_two]; field_simp
      have h := hinv _ (two_sub_mem_normOneShiftSet hkr)
      rwa [hsub, inv_div] at h

theorem mobiusSeq_ne_zero (hm : m ≠ 0)
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) : mobiusSeq a k ≠ 0 :=
  (mobiusSeq_spec hm hinv ha k).1

theorem mobiusSeq_pow_eq_one (hm : m ≠ 0)
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) : mobiusSeq a k ^ m = 1 :=
  (mobiusSeq_spec hm hinv ha k).2.1

theorem mobiusSeq_div_succ_mem_normOneShiftSet (hm : m ≠ 0)
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) :
    mobiusSeq a k / mobiusSeq a (k + 1) ∈ normOneShiftSet F m :=
  (mobiusSeq_spec hm hinv ha k).2.2

theorem mk0_mobiusSeq_mem_normOneSubgroup (hm : m ≠ 0)
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) :
    Units.mk0 (mobiusSeq a k) (mobiusSeq_ne_zero hm hinv ha k) ∈ normOneSubgroup F m := by
  rw [mem_normOneSubgroup, Units.ext_iff]
  simpa using mobiusSeq_pow_eq_one hm hinv ha k

section Config

variable {p q : ℕ}

theorem eq_geomSum_of_eq_div (hp : p.Prime) (hmdef : m = (p ^ q - 1) / (p - 1)) :
    m = ∑ i ∈ range q, p ^ i := by
  rw [hmdef, sum_range_pow_eq_div hp.two_le q]

theorem ne_zero_of_eq_div (hp : p.Prime) (hq : 0 < q) (hmdef : m = (p ^ q - 1) / (p - 1)) :
    m ≠ 0 := by
  rw [eq_geomSum_of_eq_div hp hmdef]
  exact (geomSum_pos hq).ne'

theorem mobiusSeq_spec_of_config (hp : p.Prime) (hq : q.Prime) (_hqp : q < p)
    (_hcard : Nat.card F = p ^ q) (hmdef : m = (p ^ q - 1) / (p - 1))
    (_hcop : Nat.Coprime m (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (_ha1 : a ≠ 1) (k : ℕ) :
    mobiusSeq a k ≠ 0 ∧ mobiusSeq a k ^ m = 1 ∧
      mobiusSeq a k / mobiusSeq a (k + 1) ∈ normOneShiftSet F m :=
  mobiusSeq_spec (ne_zero_of_eq_div hp hq.pos hmdef) hinv ha k

theorem norm_bot_mobiusSeq_eq_one [Fact p.Prime] [Finite F] [CharP F p] (hq : q.Prime)
    (hcard : Nat.card F = p ^ q) (hmdef : m = (p ^ q - 1) / (p - 1))
    (hinv : ∀ z ∈ normOneShiftSet F m, z⁻¹ ∈ normOneShiftSet F m)
    {a : F} (ha : a ∈ normOneShiftSet F m) (k : ℕ) :
    Algebra.norm (⊥ : Subfield F) (mobiusSeq a k) = 1 := by
  have hp : p.Prime := Fact.out
  have h := mobiusSeq_pow_eq_one (ne_zero_of_eq_div hp hq.pos hmdef) hinv ha k
  have h2 := coe_norm_bot_eq_pow_sum p F hcard (mobiusSeq a k)
  rw [← eq_geomSum_of_eq_div hp hmdef, h] at h2
  exact Subtype.ext (by simpa using h2)

end Config

end

end CFSG.FeitThompson
