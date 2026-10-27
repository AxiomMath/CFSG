module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BSd
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec8t84g3b_pow3_mul {Q : Subgroup G} {z1 z2 : G} (h1 : z1 ∈ Q) (h2 : z2 ∈ Q)
    (hz1 : z1 ^ 3 ∈ oddCoreIn Q) (hz2 : z2 ^ 3 ∈ oddCoreIn Q)
    (hc : z1 * z2 * z1⁻¹ * z2⁻¹ ∈ oddCoreIn Q) : (z1 * z2) ^ 3 ∈ oddCoreIn Q := by
  haveI : ((oddCoreIn Q).subgroupOf Q).Normal :=
    ⟨fun x hx g => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn g.2 hx⟩
  let π : ↥Q →* ↥Q ⧸ (oddCoreIn Q).subgroupOf Q := QuotientGroup.mk' _
  have key : ∀ x : ↥Q, π x = 1 ↔ (x : G) ∈ oddCoreIn Q := fun x => QuotientGroup.eq_one_iff x
  let a : ↥Q := ⟨z1, h1⟩
  let b : ↥Q := ⟨z2, h2⟩
  have ha : π a ^ 3 = 1 := by
    rw [← map_pow, key, Subgroup.coe_pow]
    exact hz1
  have hb : π b ^ 3 = 1 := by
    rw [← map_pow, key, Subgroup.coe_pow]
    exact hz2
  have hcomm : π a * π b = π b * π a := by
    have h3 : π (a * b * a⁻¹ * b⁻¹) = 1 := (key _).mpr hc
    simp only [map_mul, map_inv] at h3
    have h4 : π a * π b * (π a)⁻¹ = π b := mul_inv_eq_one.mp h3
    calc π a * π b = (π a * π b * (π a)⁻¹) * π a := by group
      _ = π b * π a := by rw [h4]
  have h5 : π ((a * b) ^ 3) = 1 := by
    rw [map_pow, map_mul, (Commute.mul_pow (show Commute (π a) (π b) from hcomm)) 3, ha, hb,
      one_mul]
  have h6 := (key _).mp h5
  rwa [Subgroup.coe_pow] at h6

theorem sec8t84g3b_conj_of_map {K : Subgroup G} {γ : G}
    (h : K.map (MulAut.conj γ).toMonoidHom = K) : ∀ u ∈ K, γ * u * γ⁻¹ ∈ K := by
  intro u hu
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom hu
  rw [h] at h1
  exact h1

theorem sec8t84g3b_norm_of_cent [Finite G] {U : Subgroup G} {z : G}
    (h : ∀ u ∈ U, z * u = u * z) : z ∈ normalizer (U : Set G) :=
  sec8t84g3b_mem_normalizer_of_conj (fun u hu => by
    rw [h u hu, mul_inv_cancel_right]
    exact hu)

theorem sec8t84g3b_comm_cancel_left {z1 z2 u : G} (hz2 : z2 * u = u * z2)
    (hm : z1 * z2 * u = u * (z1 * z2)) : z1 * u = u * z1 := by
  have h : z1 * u * z2 = u * z1 * z2 := by
    calc z1 * u * z2 = z1 * (u * z2) := by group
      _ = z1 * (z2 * u) := by rw [hz2]
      _ = z1 * z2 * u := by group
      _ = u * (z1 * z2) := hm
      _ = u * z1 * z2 := by group
  exact mul_right_cancel h

theorem sec8t84g3b_comm_cancel_right {z1 z2 u : G} (hz1 : z1 * u = u * z1)
    (hm : z1 * z2 * u = u * (z1 * z2)) : z2 * u = u * z2 := by
  have h : z1 * (z2 * u) = z1 * (u * z2) := by
    calc z1 * (z2 * u) = z1 * z2 * u := by group
      _ = u * (z1 * z2) := hm
      _ = (u * z1) * z2 := by group
      _ = (z1 * u) * z2 := by rw [hz1]
      _ = z1 * (u * z2) := by group
  exact mul_left_cancel h

end CFSG.OddStandard.SmallF3.Omega
