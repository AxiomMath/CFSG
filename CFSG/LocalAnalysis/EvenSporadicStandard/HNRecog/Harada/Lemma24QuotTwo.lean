module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem card_two_subgroup_le_quot {Y : Type} [Group Y] [Finite Y] {a : Y} [(zpowers a).Normal]
    (ha3 : orderOf a = 3) (hY : ∀ R : Subgroup Y, IsPGroup 2 R → Nat.card R ≤ 64) :
    ∀ R : Subgroup (Y ⧸ zpowers a), IsPGroup 2 R → Nat.card R ≤ 64 := by
  classical
  intro R hR
  have hquot : Nat.card Y = Nat.card (Y ⧸ zpowers a) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_zpowers, ha3]
  have hSY : 2 ^ (Nat.card Y).factorization 2 ≤ 64 := by
    have h := hY (default : Sylow 2 Y) (default : Sylow 2 Y).isPGroup'
    rwa [Sylow.card_eq_multiplicity (default : Sylow 2 Y)] at h
  have hv2 : (Nat.card Y).factorization 2
      = (Nat.card (Y ⧸ zpowers a)).factorization 2 := by
    have hQ0 : Nat.card (Y ⧸ zpowers a) ≠ 0 := Nat.card_pos.ne'
    have h32 : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [hquot, Nat.factorization_mul hQ0 (by norm_num : (3 : ℕ) ≠ 0),
      Finsupp.add_apply, h32, add_zero]
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  calc Nat.card R ≤ Nat.card T := Subgroup.card_le_of_le hRT
    _ = 2 ^ (Nat.card (Y ⧸ zpowers a)).factorization 2 := Sylow.card_eq_multiplicity T
    _ ≤ 64 := by rw [← hv2]; exact hSY

end CFSG.EvenSporadicStandard.HNRecog.Harada
