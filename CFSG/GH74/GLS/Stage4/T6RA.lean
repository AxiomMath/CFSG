module

public import CFSG.GH74.GLS.Stage4.T6Count

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev RA (N : T2N3 G) (p : ℕ) (u : G) : Subgroup G := R₂ N p ⊓ Subgroup.centralizer {u}

abbrev RB (N : T2N3 G) (p : ℕ) (u : G) : Subgroup G := R₂ N p ⊓ Subgroup.centralizer {N.z * u}

theorem X₂_u_fix {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {x : G} (hx : x ∈ N.X₂)
    (hxu : x * u = u * x) : x = 1 := by
  have hpg := R₂_pGroup N h.prime
  have h1 := h.sec5.loc.u_inv_X₂ x hx
  have h2 : u * x * u⁻¹ = x := by
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [hxu]
      _ = x := by group
  have h3 : x * x = 1 := by
    have : x = x⁻¹ := by rw [← h1, h2]
    calc x * x = x * x⁻¹ := by rw [← this]
      _ = 1 := by group
  have hodd := t6_odd_of_pGroup h.prime h.p_ne_two hpg (X₂_le_R₂ h hx)
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
  · exact orderOf_eq_one_iff.1 h4
  · rw [h4] at hodd; exact absurd hodd (by decide)

theorem RA_zconj {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {r : G} (hr : r ∈ RA N p u) :
    N.z * r * N.z⁻¹ ∈ RA N p u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  refine ⟨R₂_norm N p (z_mem_M₂ h) hr.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hru : r * u = u * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  show N.z * r * N.z⁻¹ * u = u * (N.z * r * N.z⁻¹)
  calc N.z * r * N.z⁻¹ * u = N.z * r * (N.z⁻¹ * u) := by group
    _ = N.z * r * (u * N.z⁻¹) := by
      have : N.z⁻¹ * u = u * N.z⁻¹ := by
        have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
        rw [hz]; exact hzu
      rw [this]
    _ = N.z * (r * u) * N.z⁻¹ := by group
    _ = N.z * (u * r) * N.z⁻¹ := by rw [hru]
    _ = (N.z * u) * r * N.z⁻¹ := by group
    _ = (u * N.z) * r * N.z⁻¹ := by rw [hzu]
    _ = u * (N.z * r * N.z⁻¹) := by group

theorem RA_inv {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    (∀ r ∈ RA N p u, N.z * r * N.z⁻¹ = r⁻¹) ∧ ∀ r ∈ RA N p u, ∀ s ∈ RA N p u, r * s = s * r := by
  obtain ⟨hz2, -⟩ := zu_facts h
  exact t6_inv_of_fpf (A := RA N p u) hz2 (fun r hr => RA_zconj h hr) (by
    intro r hr hfix
    have hrX : r ∈ N.X₂ := R₂_Cz h r hr.1 hfix
    exact X₂_u_fix h hrX (Subgroup.mem_centralizer_singleton_iff.1 hr.2))

theorem RA_H {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {x : G} (hx : x ∈ N.H) {r : G}
    (hr : r ∈ RA N p u) : x * r * x⁻¹ ∈ RA N p u := by
  refine ⟨R₂_norm N p (H_le_M₂ h hx) hr.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hru : r * u = u * r := Subgroup.mem_centralizer_singleton_iff.1 hr.2
  have hxu : x * u = u * x := h.sec5.loc.H_comm x hx u h.sec5.loc.u_mem_H
  show x * r * x⁻¹ * u = u * (x * r * x⁻¹)
  calc x * r * x⁻¹ * u = x * r * (x⁻¹ * u) := by group
    _ = x * r * (u * x⁻¹) := by
      have : x⁻¹ * u = u * x⁻¹ := by
        calc x⁻¹ * u = x⁻¹ * (u * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * u) * x⁻¹ := by rw [hxu]
          _ = u * x⁻¹ := by group
      rw [this]
    _ = x * (r * u) * x⁻¹ := by group
    _ = x * (u * r) * x⁻¹ := by rw [hru]
    _ = (x * u) * r * x⁻¹ := by group
    _ = (u * x) * r * x⁻¹ := by rw [hxu]
    _ = u * (x * r * x⁻¹) := by group

theorem RA_pGroup {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) : IsPGroup p ↥(RA N p u) :=
  (R₂_pGroup N h.prime).to_le inf_le_left

theorem RA_card_eq_RB {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    Nat.card ↥(RB N p u) = Nat.card ↥(RA N p u) := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hw₁K : N.w₁ ∈ N.K₁ := h.sec5.loc.w₁_mem
  have hw₁M : N.w₁ ∈ M₂ N := K₁_le_M₂ h hw₁K
  have hconj : N.w₁ * u * N.w₁⁻¹ = N.z * u := by
    rw [h.sec5.loc.w₁_u, hzu]
  have := t6_card_cent_conj (R := R₂ N p) (w := N.w₁) (fun r hr => R₂_norm N p hw₁M hr)
    (fun r hr => by simpa using R₂_norm N p ((M₂ N).inv_mem hw₁M) hr) u
  rw [hconj] at this
  exact this.symm

theorem R₂_card_RA {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) :
    Nat.card ↥(R₂ N p) = N.q₂ * Nat.card ↥(RA N p u) ^ 2 := by
  rw [R₂_card_eq h]
  have := RA_card_eq_RB h
  change N.q₂ * Nat.card ↥(RA N p u) * Nat.card ↥(RB N p u) = _
  rw [this]; ring

end CFSG.GH74.GLS.Stage4.Rest.T6
