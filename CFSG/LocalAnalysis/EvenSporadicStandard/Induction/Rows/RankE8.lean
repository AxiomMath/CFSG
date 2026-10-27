module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard

theorem zpow_involution {X : Type*} [Group X] {a : X} (ha : a * a = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hk, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem three_le_pRank_of_three_involutions {X : Type} [Group X] [Finite X] {a b c : X}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (h1 : a ≠ 1) (h2 : b ≠ 1) (h3 : b ≠ a)
    (h4 : c ≠ 1) (h5 : c ≠ a) (h6 : c ≠ b) (h7 : c ≠ a * b) : 3 ≤ CFSG.pRank 2 X := by
  have hzx : b ∉ Subgroup.zpowers a := by
    rintro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rcases zpow_involution ha k with h | h
    · exact h2 (hk.symm.trans h)
    · exact h3 (hk.symm.trans h)
  have hcxz : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    intro hmem
    have hle : Subgroup.zpowers b ≤ centralizer (Subgroup.zpowers a : Set X) := by
      rw [Subgroup.zpowers_le]
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute a b from hab).zpow_left k).eq
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rcases zpow_involution ha k with h | h <;> rcases zpow_involution hb l with h' | h' <;>
      rw [h, h'] at hyz
    · exact h4 (by simpa using hyz)
    · exact h6 (by simpa using hyz)
    · exact h5 (by simpa using hyz)
    · exact h7 hyz
  have h := CFSG.RankThree.PartOne.Torsion37.three_le_pRank_of_commuting (G := X) Nat.prime_two
    (H := ⊤) (x := a) (z := b) (c := c) (mem_top _) (mem_top _) (mem_top _) hab hac hbc
    (by rw [sq]; exact ha) (by rw [sq]; exact hb) (by rw [sq]; exact hc) h1 h2 hzx hcxz
  rwa [pRank_two_eq_of_mulEquiv' (Subgroup.topEquiv (G := X))] at h

end CFSG.EvenSporadicStandard.Induction
