module

public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedSylow
public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedCosets

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

open Subgroup

theorem sylow_abelian_and_index_bound [Finite G] {θ : MulAut G} (hθ : θ * θ = 1)
    (hS : Nat.card G ≤ 4 * Nat.card {g : G // θ g = g⁻¹}) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (P : Sylow p G) :
    (∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a) ∧
      (centralizer ((P : Subgroup G) : Set G)).index * (p - 4) ≤ 4 * (p - 1) := by
  classical
  obtain ⟨θ', hθ', hcard, hPS⟩ := exists_inverting_automorphism_of_sylow hθ hS hp P
  have habel : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a :=
    mul_comm_of_apply_eq_inv hPS
  refine ⟨habel, ?_⟩
  have hbound := card_inverted_bound (θ := θ') P.isPGroup' hPS
  rw [hcard] at hbound
  set cardS : ℕ := Nat.card {g : G // θ g = g⁻¹} with hcardS
  set cardC : ℕ := Nat.card (centralizer ((P : Subgroup G) : Set G)) with hcardC
  set cardG : ℕ := Nat.card G with hcardG
  set m : ℕ := (centralizer ((P : Subgroup G) : Set G)).index with hm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hidx : m * cardC = cardG := by
    rw [hm, hcardC, hcardG]
    exact Subgroup.index_mul_card _
  have hCpos : 0 < cardC := by
    rw [hcardC]
    exact Nat.card_pos
  have hq4 : 5 + q - 4 = q + 1 := by omega
  have hq1 : 5 + q - 1 = q + 4 := by omega
  have hkey : (q + 1) * cardS ≤ (q + 4) * cardC := by
    nlinarith [hbound, hS]
  have hstep : (q + 1) * cardG ≤ 4 * ((q + 4) * cardC) := by
    calc (q + 1) * cardG ≤ (q + 1) * (4 * cardS) := Nat.mul_le_mul_left _ hS
      _ = 4 * ((q + 1) * cardS) := by ring
      _ ≤ 4 * ((q + 4) * cardC) := Nat.mul_le_mul_left _ hkey
  rw [← hidx] at hstep
  have hstep' : (m * (q + 1)) * cardC ≤ (4 * (q + 4)) * cardC := by
    calc (m * (q + 1)) * cardC = (q + 1) * (m * cardC) := by ring
      _ ≤ 4 * ((q + 4) * cardC) := hstep
      _ = (4 * (q + 4)) * cardC := by ring
  have hfinal : m * (q + 1) ≤ 4 * (q + 4) := Nat.le_of_mul_le_mul_right hstep' hCpos
  rw [hq4, hq1]
  exact hfinal

end CFSG.GroupTheory.SmallFixedTwoGroup
