module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Co2Std

open Subgroup

variable {G : Type*} [Group G]

theorem le_centralizer_zpowers_of_centralizer_eq {L : Subgroup G} {z : G}
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) : zpowers z ≤ centralizer (L : Set G) := by
  rw [zpowers_le]
  rw [mem_centralizer_iff]
  intro l hl
  have : l ∈ centralizer ({z} : Set G) := by rw [hC]; exact mem_sup_left hl
  exact mem_centralizer_singleton_iff.1 this

theorem not_sq_eq_self {L : Subgroup G} {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) (hd : Disjoint L (zpowers z)) (w : G) :
    w * w ≠ z := by
  intro hw
  have hwz : w * z = z * w := by
    rw [← hw]
    group
  have hwC : w ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hwz
  rw [hC] at hwC
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (le_centralizer_zpowers_of_centralizer_eq hC) hwC
  have hb2 : b * b = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    have hzp : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz2]
    rw [← zpow_add, ← two_mul, zpow_mul, hzp, one_zpow]
  have hlb : l * b = b * l := (mem_centralizer_iff.1 (le_centralizer_zpowers_of_centralizer_eq hC
    hb) l hl)
  have hsq : l * b * (l * b) = l * l := by
    calc l * b * (l * b) = l * (b * l) * b := by group
      _ = l * (l * b) * b := by rw [← hlb]
      _ = l * l * (b * b) := by group
      _ = l * l := by rw [hb2, mul_one]
  have hzL : z ∈ L := by rw [← hw, hsq]; exact mul_mem hl hl
  exact hz1 (mem_bot.1 (hd.le_bot ⟨hzL, mem_zpowers z⟩))

theorem not_sq_eq_of_isConj {L : Subgroup G} {z x : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) (hd : Disjoint L (zpowers z))
    (hx : IsConj z x) (w : G) : w * w ≠ x := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  intro hw
  refine not_sq_eq_self hz1 hz2 hC hd (g⁻¹ * w * g) ?_
  calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hw, hg]
    _ = z := by group

theorem not_isConj_of_mem_of_sq {L : Subgroup G} {z v w : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) (hd : Disjoint L (zpowers z))
    (hvw : w * w = v) : ¬ IsConj z v := fun hv => not_sq_eq_of_isConj hz1 hz2 hC hd hv w hvw

end CFSG.EvenSporadicStandard.Co2Std
