module

public import Certificates.Certificate441665

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

section Cert

variable (hP : Nat.card ↥P1408 = 177408000)

include hP

theorem r0Facts : Certificates.R0Facts := Certificates.certificate441665 hP

theorem r0_card : Nat.card ↥(wordSubgroupP nWords1) = 2 ^ 8 := (r0Facts hP).r0_card

theorem r0_le_centralizer : wordSubgroupP nWords1 ≤ centralizer ({pZ} : Set ↥P1408) :=
  (r0Facts hP).r0_le_centralizer

theorem r0_normal :
    ∀ c ∈ centralizer ({pZ} : Set ↥P1408), ∀ x ∈ wordSubgroupP nWords1,
      c * x * c⁻¹ ∈ wordSubgroupP nWords1 :=
  (r0Facts hP).r0_normal

theorem r0_sq : ∀ x ∈ wordSubgroupP nWords1, x ^ 2 ∈ zpowers pZ := (r0Facts hP).r0_sq

private theorem commute_of_mem_wordSubgroupP_zpowers {x : ↥P1408}
    (hx : x ∈ wordSubgroupP nWords1) {a : ↥P1408} (ha : a ∈ zpowers pZ) :
    Commute x a := by
  have hx' : x ∈ centralizer ({pZ} : Set ↥P1408) := r0_le_centralizer hP hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hc : Commute x pZ :=
    (Subgroup.mem_centralizer_iff.1 hx' pZ (Set.mem_singleton pZ)).symm
  exact hc.zpow_right k

theorem r0_comm : ∀ x ∈ wordSubgroupP nWords1, ∀ y ∈ wordSubgroupP nWords1,
    x * y * x⁻¹ * y⁻¹ ∈ zpowers pZ := by
  intro x hx y hy
  have hx2 : x ^ 2 ∈ zpowers pZ := r0_sq hP x hx
  have hy2 : y ^ 2 ∈ zpowers pZ := r0_sq hP y hy
  have hxin : (x ^ 2)⁻¹ ∈ zpowers pZ := inv_mem hx2
  have hyin : (y ^ 2)⁻¹ ∈ zpowers pZ := inv_mem hy2
  have hxy2 : (x * y) ^ 2 ∈ zpowers pZ := r0_sq hP (x * y) (mul_mem hx hy)
  have hya : Commute y ((x ^ 2)⁻¹) := commute_of_mem_wordSubgroupP_zpowers hP hy hxin
  have hxinv : x⁻¹ = x * (x ^ 2)⁻¹ := by group
  have hyinv : y⁻¹ = y * (y ^ 2)⁻¹ := by group
  have key : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by
    rw [hxinv, hyinv]
    calc x * y * (x * (x ^ 2)⁻¹) * (y * (y ^ 2)⁻¹)
        = x * y * x * ((x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by group
      _ = x * y * x * (y * (x ^ 2)⁻¹) * (y ^ 2)⁻¹ := by rw [← hya.eq]
      _ = x * y * x * y * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by group
      _ = (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ := by
        have hxy' : x * y * x * y = (x * y) ^ 2 := by rw [pow_two]; group
        rw [hxy']
  rw [key]
  exact mul_mem (mul_mem hxy2 hxin) hyin

theorem r0_faith :
    ∀ c ∈ centralizer ({pZ} : Set ↥P1408),
      (∀ x ∈ wordSubgroupP nWords1, c * x * c⁻¹ * x⁻¹ ∈ zpowers pZ) →
        c ∈ wordSubgroupP nWords1 :=
  (r0Facts hP).r0_faith

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
