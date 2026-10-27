module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_eq_card_mul_card_map (N : Subgroup G) [N.Normal] {A : Subgroup G} (hNA : N ≤ A) :
    Nat.card A = Nat.card N * Nat.card (A.map (QuotientGroup.mk' N)) := by
  have hker : (QuotientGroup.mk' N).ker ≤ A := by rwa [QuotientGroup.ker_mk']
  have hidx := Subgroup.index_map_eq A (QuotientGroup.mk'_surjective N) hker
  have h1 := Subgroup.card_mul_index A
  have h2 := Subgroup.card_mul_index (A.map (QuotientGroup.mk' N))
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hidx] at h2
  have hpos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card A * A.index = Nat.card G := h1
    _ = Nat.card (G ⧸ N) * Nat.card N := h3
    _ = (Nat.card (A.map (QuotientGroup.mk' N)) * A.index) * Nat.card N := by rw [h2]
    _ = Nat.card N * Nat.card (A.map (QuotientGroup.mk' N)) * A.index := by ring

theorem relIndex_eq_relIndex_map (N : Subgroup G) [N.Normal] {A₁ A₂ : Subgroup G} (h : A₂ ≤ A₁)
    (hN : N ≤ A₂) :
    A₂.relIndex A₁ = ((A₂.map (QuotientGroup.mk' N)).relIndex (A₁.map (QuotientGroup.mk' N))) := by
  have e1 := Subgroup.relIndex_mul_card A₂ A₁
  have e2 := Subgroup.relIndex_mul_card (A₂.map (QuotientGroup.mk' N))
    (A₁.map (QuotientGroup.mk' N))
  rw [inf_eq_left.mpr h] at e1
  rw [inf_eq_left.mpr (Subgroup.map_mono h)] at e2
  rw [card_eq_card_mul_card_map N (hN.trans h), card_eq_card_mul_card_map N hN] at e1
  have hpos : 0 < Nat.card (A₂.map (QuotientGroup.mk' N)) := Nat.card_pos
  have hposN : 0 < Nat.card N := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [e2]
  apply Nat.eq_of_mul_eq_mul_left hposN
  rw [← e1]
  ring

omit [Finite G] in
theorem map_inf_centralizer_of_odd (N : Subgroup G) [N.Normal] (hcen : N ≤ center G)
    (hodd : Odd (Nat.card N)) (A : Subgroup G) {s : G} (hs : s * s = 1) :
    (A ⊓ centralizer ({s} : Set G)).map (QuotientGroup.mk' N) =
      A.map (QuotientGroup.mk' N) ⊓ centralizer ({(QuotientGroup.mk' N) s} : Set (G ⧸ N)) := by
  apply le_antisymm
  · refine le_inf (Subgroup.map_mono inf_le_left) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
  · rintro x ⟨⟨a, ha, rfl⟩, hx⟩
    refine ⟨a, Subgroup.mem_inf.mpr ⟨ha, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx' : ((QuotientGroup.mk' N) a) ∈
        centralizer ({(QuotientGroup.mk' N) s} : Set (G ⧸ N)) := hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hx'
    have hz : a * s * a⁻¹ * s⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      rw [MonoidHom.mem_ker]
      have hxx : (QuotientGroup.mk' N) (a * s) = (QuotientGroup.mk' N) (s * a) := hx'
      simp only [map_mul, map_inv] at hxx ⊢
      rw [hxx]
      group
    set z := a * s * a⁻¹ * s⁻¹ with hzdef
    have hzc : ∀ g, g * z = z * g := fun g => Subgroup.mem_center_iff.mp (hcen hz) g
    have hasa : a * s * a⁻¹ = z * s := by rw [hzdef]; group
    have hsq : (z * s) * (z * s) = z * z := by
      calc (z * s) * (z * s) = z * (s * z) * s := by group
        _ = z * (z * s) * s := by rw [hzc s]
        _ = z * z * (s * s) := by group
        _ = z * z := by rw [hs, mul_one]
    have hconj : (a * s * a⁻¹) * (a * s * a⁻¹) = 1 := by
      calc (a * s * a⁻¹) * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
        _ = 1 := by rw [hs]; group
    rw [hasa, hsq] at hconj
    have hzodd : Odd (orderOf z) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hz)
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · rw [h2] at hzodd
        exact absurd hzodd (by decide)
    have : a * s * a⁻¹ = s := by rw [hasa, hz1, one_mul]
    calc a * s = (a * s * a⁻¹) * a := by group
      _ = s * a := by rw [this]

omit [Finite G] in
theorem map_inf_of_ker_le (N : Subgroup G) [N.Normal] {H₁ H₂ : Subgroup G} (h₂ : N ≤ H₂) :
    (H₁ ⊓ H₂).map (QuotientGroup.mk' N) =
      H₁.map (QuotientGroup.mk' N) ⊓ H₂.map (QuotientGroup.mk' N) := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
  have hker : a⁻¹ * b ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, ← hab]
    group
  have haH₂ : a ∈ H₂ := by
    have : a = b * (a⁻¹ * b)⁻¹ := by group
    rw [this]
    exact H₂.mul_mem hb (H₂.inv_mem (h₂ hker))
  exact ⟨a, Subgroup.mem_inf.mpr ⟨ha, haH₂⟩, rfl⟩

end CFSG.GH74.Uniqueness
