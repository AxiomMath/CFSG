module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_unique_E8 {t : G} {E K B A : Subgroup G} (ht : t * t = 1)
    (hE8 : IsElemAb2 E 8) (hK : K = zpowers t ⊔ E) (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hB : E ⊓ centralizer ({t} : Set G) = B) (hB4 : Nat.card B = 16)
    (hA : A ≤ K) (hA8 : IsElemAb2 A 8) : A = E := by
  by_contra hAE
  have hEsubK : E ≤ K := by rw [hK]; exact le_sup_right
  have hnotle : ¬ A ≤ E := fun hle =>
    hAE (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hE8.2, hA8.2])))
  obtain ⟨a, haA, haE⟩ :=
    Set.not_subset.mp (show ¬ (A : Set G) ⊆ (E : Set G) from hnotle)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htnmem : t ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact htn e
    · intro he
      have hconj : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by simp only [mul_assoc]
          _ = e := by rw [ht, one_mul, mul_one]
      have h2 := htn (t * e * t⁻¹) he
      rwa [hconj] at h2
  have hzpnorm : zpowers t ≤ Subgroup.normalizer (E : Set G) := Subgroup.zpowers_le.mpr htnmem
  have hKm : (K : Set G) = (zpowers t : Set G) * (E : Set G) := by
    rw [hK]
    exact Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) E hzpnorm
  have haKm : a ∈ (zpowers t : Set G) * (E : Set G) := by
    rw [← hKm]; exact hA haA
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp haKm
  have hy_ne_one : y ≠ 1 := by
    intro h
    apply haE
    rw [h, one_mul] at hyz
    exact hyz ▸ hz
  have hy_cases : y = 1 ∨ y = t := by
    change y ∈ Subgroup.zpowers t at hy
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · left
      rw [hk, zpow_mul, zpow_two, ht, one_zpow]
    · right
      rw [hk, zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one]
  have hy_eq : y = t := by
    rcases hy_cases with h | h
    · exact absurd h hy_ne_one
    · exact h
  have haz : a = t * z := by rw [← hyz, hy_eq]
  have hleB : E ⊓ A ≤ B := by
    rw [← hB]
    intro w hw
    obtain ⟨hwE, hwA⟩ := hw
    refine ⟨hwE, ?_⟩
    change w ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm_a : w * a = a * w := hA8.1.comm hwA haA
    have hcomm_z : w * z = z * w := hE8.1.comm hwE hz
    have key : (w * t) * z = (t * w) * z := by
      calc (w * t) * z = w * (t * z) := by rw [mul_assoc]
        _ = w * a := by rw [← haz]
        _ = a * w := hcomm_a
        _ = (t * z) * w := by rw [haz]
        _ = t * (z * w) := by rw [mul_assoc]
        _ = t * (w * z) := by rw [← hcomm_z]
        _ = (t * w) * z := by rw [← mul_assoc]
    exact mul_right_cancel key
  have hupper : Nat.card ↥(E ⊓ A) ≤ 16 := by
    have h := Subgroup.card_le_of_le hleB
    rwa [hB4] at h
  have hrelA : (E ⊓ A).relIndex A * Nat.card ↥(E ⊓ A) = Nat.card A := by
    have h := Subgroup.relIndex_mul_card (H := E ⊓ A) (K := A)
    rwa [inf_eq_left.mpr inf_le_right] at h
  have hrel_eq : (E ⊓ A).relIndex A = E.relIndex A := Subgroup.inf_relIndex_right E A
  have hrelK_mul : E.relIndex K * Nat.card E = Nat.card K := by
    have h := Subgroup.relIndex_mul_card (H := E) (K := K)
    rwa [inf_eq_left.mpr hEsubK] at h
  have hEpos : 0 < Nat.card E := by rw [hE8.2]; norm_num
  have hKpos : 0 < Nat.card K := lt_of_lt_of_le hEpos (Subgroup.card_le_of_le hEsubK)
  have hne : E.relIndex K ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrelK_mul
    exact hKpos.ne' hrelK_mul.symm
  have hrelAK : E.relIndex A ≤ E.relIndex K := Subgroup.relIndex_le_of_le_right hA hne
  have hcardt : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht))
  have hzpK : zpowers t ≤ K := by rw [hK]; exact le_sup_left
  have hsurj : Function.Surjective (fun p : (zpowers t) × E =>
      (⟨(p.1 : G) * (p.2 : G), K.mul_mem (hzpK p.1.2) (hEsubK p.2.2)⟩ : K)) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (zpowers t : Set G) * (E : Set G) := by
      rw [← hKm]; exact hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hx'
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), Subtype.ext hyz⟩
  have hKcard : Nat.card K ≤ 2 * Nat.card E := by
    have h1 : Nat.card K ≤ Nat.card ((zpowers t) × E) :=
      Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod] at h1
    calc Nat.card K ≤ Nat.card (zpowers t) * Nat.card E := h1
      _ ≤ 2 * Nat.card E := Nat.mul_le_mul_right (Nat.card E) hcardt
  have hrelK2 : E.relIndex K ≤ 2 := by
    by_contra hx
    have hx3 : 3 ≤ E.relIndex K := by omega
    have h3 : 3 * Nat.card E ≤ Nat.card K := by
      calc 3 * Nat.card E ≤ E.relIndex K * Nat.card E :=
            Nat.mul_le_mul_right (Nat.card E) hx3
        _ = Nat.card K := hrelK_mul
    have h32 : 3 * Nat.card E ≤ 2 * Nat.card E := h3.trans hKcard
    omega
  have hrel_le : (E ⊓ A).relIndex A ≤ 2 := by
    rw [hrel_eq]
    exact hrelAK.trans hrelK2
  have hle2 : 2 ^ 8 ≤ 2 * Nat.card ↥(E ⊓ A) := by
    calc 2 ^ 8 = Nat.card A := hA8.2.symm
      _ = (E ⊓ A).relIndex A * Nat.card ↥(E ⊓ A) := hrelA.symm
      _ ≤ 2 * Nat.card ↥(E ⊓ A) := Nat.mul_le_mul_right (Nat.card ↥(E ⊓ A)) hrel_le
  have hlower : 2 ^ 7 ≤ Nat.card ↥(E ⊓ A) := by
    have h : 2 ^ 8 ≤ 2 * Nat.card ↥(E ⊓ A) := hle2
    omega
  have hcontra : (2 : ℕ) ^ 7 ≤ 16 := hlower.trans hupper
  omega

end CFSG.OddStandard.SmallF3.Omega
