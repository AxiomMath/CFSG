module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G]

private theorem inv_mul_mem_of_relIndex_two_aux {N K : Subgroup G} (h : N.relIndex K = 2)
    {a b : G} (ha : a ∈ K) (hb : b ∈ K) (hna : a ∉ N) (hnb : b ∉ N) : a⁻¹ * b ∈ N := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp h
  have key : ∀ z : G, (hz : z ∈ K) → z ∉ N →
      (⟨z⁻¹, K.inv_mem hz⟩ : ↥K) * c ∈ N.subgroupOf K := by
    intro z hz hzN
    have hx : (⟨z⁻¹, K.inv_mem hz⟩ : ↥K) ∉ N.subgroupOf K := fun h' =>
      hzN (by simpa using N.inv_mem (Subgroup.mem_subgroupOf.mp h'))
    rcases hc ⟨z⁻¹, K.inv_mem hz⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hx
  have h1 := key a ha hna
  have h2 := key b hb hnb
  have h3 := (N.subgroupOf K).mul_mem h1 ((N.subgroupOf K).inv_mem h2)
  have h4 : (⟨a⁻¹, K.inv_mem ha⟩ : ↥K) * c * ((⟨b⁻¹, K.inv_mem hb⟩ : ↥K) * c)⁻¹ =
      ⟨a⁻¹, K.inv_mem ha⟩ * ⟨b⁻¹, K.inv_mem hb⟩⁻¹ := by simp [mul_assoc]
  rw [h4] at h3
  simpa using Subgroup.mem_subgroupOf.mp h3

theorem sq_mem_of_relIndex_two {H K : Subgroup G} (hHK : H ≤ K) (h2 : H.relIndex K = 2) {x : G}
    (hx : x ∈ K) : x ^ 2 ∈ H := by
  have := Subgroup.sq_mem_of_index_two (H := H.subgroupOf K) h2 (⟨x, hx⟩ : K)
  simpa [Subgroup.mem_subgroupOf] using this

theorem eq_of_relIndex_two {H K X : Subgroup G} (hHX : H ≤ X) (hXK : X ≤ K)
    (h2 : H.relIndex K = 2) (hXH : ¬ X ≤ H) : X = K := by
  have hprod := Subgroup.relIndex_mul_relIndex H X K hHX hXK
  rw [h2] at hprod
  have hne1 : H.relIndex X ≠ 1 := fun h => hXH (Subgroup.relIndex_eq_one.mp h)
  have hdvd : H.relIndex X ∣ 2 := ⟨X.relIndex K, hprod.symm⟩
  have hle : H.relIndex X ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have h2' : H.relIndex X = 2 := by
    rcases Nat.lt_or_ge (H.relIndex X) 2 with hlt | hge
    · rcases Nat.eq_zero_or_pos (H.relIndex X) with h0 | hpos
      · rw [h0] at hprod
        simp at hprod
      · have h1 : H.relIndex X = 1 := by omega
        exact absurd h1 hne1
    · exact le_antisymm hle hge
  have hXK1 : X.relIndex K = 1 := by
    have h : 2 * X.relIndex K = 2 * 1 := by rw [mul_one]; rwa [h2'] at hprod
    exact Nat.mul_left_cancel (by decide) h
  exact le_antisymm hXK (Subgroup.relIndex_eq_one.mp hXK1)

theorem eq_sup_zpowers_of_relIndex_two {H K X : Subgroup G} (hXK : X ≤ K)
    (h2 : H.relIndex K = 2) {d : G} (hd : d ∈ X) (hdH : d ∉ H) : X = (X ⊓ H) ⊔ zpowers d := by
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr hd))
  intro y hy
  by_cases hyH : y ∈ H
  · exact Subgroup.mem_sup_left ⟨hy, hyH⟩
  · have hmem := inv_mul_mem_of_relIndex_two_aux h2 (hXK hd) (hXK hy) hdH hyH
    have hdyX : d⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hd) hy
    have hy_eq : y = d * (d⁻¹ * y) := by simp
    rw [hy_eq, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers d) ⟨hdyX, hmem⟩

end CFSG.OddStandard.HigherRank.YamadaG23
