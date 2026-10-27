module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup Equiv

theorem normalizer_zpowers_eq_centralizer_of_orderOf_eq_two {G : Type*} [Group G] {y : G}
    (hy : orderOf y = 2) :
    normalizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  ext g
  rw [mem_centralizer_singleton_iff, mem_normalizer_iff]
  constructor
  · intro hg
    have hmem : g * y * g⁻¹ ∈ zpowers y := (hg y).mp (mem_zpowers y)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hy' : ∀ k : ℤ, y ^ k = 1 ∨ y ^ k = y := by
      intro k
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · left
        rw [zpow_mul, zpow_two, hyy, one_zpow]
      · right
        rw [zpow_add, zpow_mul, zpow_two, hyy, one_zpow, one_mul, zpow_one]
    rcases hy' k with h | h
    · exfalso
      rw [h] at hk
      have : y = 1 := by
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = 1 := by rw [← hk]; group
      rw [this, orderOf_one] at hy
      norm_num at hy
    · rw [h] at hk
      calc g * y = (g * y * g⁻¹) * g := by group
        _ = y * g := by rw [← hk]
  · intro hg w
    have hc : ∀ k : ℤ, g * y ^ k * g⁻¹ = y ^ k := fun k => by
      rw [(Commute.zpow_right (show Commute g y from hg) k).eq]; group
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      rw [hc k]
      exact zpow_mem_zpowers y k
    · intro hw
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw
      have : w = y ^ k := by
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = g⁻¹ * y ^ k * g := by rw [hk]
          _ = y ^ k := by
            rw [((Commute.zpow_right (show Commute g y from hg) k).inv_left).eq]; group
      rw [this]
      exact zpow_mem_zpowers y k

end CFSG.ComponentClassification.Sol78
