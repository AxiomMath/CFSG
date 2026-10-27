module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace NF58

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_part_mul_odd (c : G) :
    ∃ a ∈ zpowers c, ∃ b ∈ zpowers c, c = a * b ∧ (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set x := Nat.gcdA (2 ^ k) m
  set y := Nat.gcdB (2 ^ k) m
  refine ⟨c ^ ((m : ℤ) * y), ⟨_, rfl⟩, c ^ ((2 ^ k : ℕ) * x : ℤ), ⟨_, rfl⟩, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← _root_.zpow_add, add_comm, ← hbez, zpow_one]
  · rw [← zpow_natCast, ← _root_.zpow_mul, show ((m : ℤ) * y) * ((2 ^ k : ℕ) : ℤ) =
        ((orderOf c : ℕ) : ℤ) * y by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, _root_.one_zpow]
  · refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← _root_.zpow_mul, show ((2 ^ k : ℕ) * x : ℤ) * (m : ℤ) =
        ((orderOf c : ℕ) : ℤ) * x by rw [hkm]; push_cast; ring, _root_.zpow_mul, zpow_natCast,
      pow_orderOf_eq_one, _root_.one_zpow]

end NF58

end CFSG.ComponentClassification.GSThmB
