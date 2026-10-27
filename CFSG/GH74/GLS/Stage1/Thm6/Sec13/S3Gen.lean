module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_sq {N : Subgroup G} {s : G} (hs : s * s ∈ N)
    (hN : ∀ q ∈ N, s * q * s⁻¹ ∈ N) {g : G} :
    g ∈ N ⊔ zpowers s ↔ ∃ q ∈ N, g = q ∨ g = q * s := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ q ∈ N, g = q ∨ g = q * s}
        one_mem' := ⟨1, N.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          obtain ⟨u, hu, ha | ha⟩ := ha <;> obtain ⟨w, hw, hb | hb⟩ := hb <;> rw [ha, hb]
          · exact ⟨u * w, N.mul_mem hu hw, Or.inl rfl⟩
          · exact ⟨u * w, N.mul_mem hu hw, Or.inr (by rw [mul_assoc])⟩
          · refine ⟨u * (s * w * s⁻¹), N.mul_mem hu (hN w hw), Or.inr ?_⟩
            group
          · refine ⟨u * (s * w * s⁻¹) * (s * s), N.mul_mem (N.mul_mem hu (hN w hw)) hs, Or.inl ?_⟩
            group
        inv_mem' := by
          intro a ha
          obtain ⟨u, hu, ha | ha⟩ := ha <;> rw [ha]
          · exact ⟨u⁻¹, N.inv_mem hu, Or.inl rfl⟩
          · refine ⟨(s * s)⁻¹ * (s * u⁻¹ * s⁻¹), N.mul_mem (N.inv_mem hs)
              (hN _ (N.inv_mem hu)), Or.inr ?_⟩
            group }
    have hle : N ⊔ zpowers s ≤ S := by
      refine sup_le (fun v hv => ⟨v, hv, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, N.one_mem, Or.inr (by simp)⟩
    exact hle hg
  · rintro ⟨q, hq, hg | hg⟩ <;> rw [hg]
    · exact Subgroup.mem_sup_left hq
    · exact (N ⊔ zpowers s).mul_mem (Subgroup.mem_sup_left hq)
        (Subgroup.mem_sup_right (mem_zpowers s))

theorem card_sup_zpowers_sq [Finite G] {N : Subgroup G} {s : G} (hs : s * s ∈ N)
    (hN : ∀ q ∈ N, s * q * s⁻¹ ∈ N) (hsN : s ∉ N) :
    Nat.card ↥(N ⊔ zpowers s) = 2 * Nat.card N := by
  have hle : N ≤ N ⊔ zpowers s := le_sup_left
  have hrel : N.relIndex (N ⊔ zpowers s) = 2 := by
    have hdvd : N.relIndex (N ⊔ zpowers s) ∣ 2 := by
      rw [relIndex_dvd_two_iff]
      refine ⟨s, Subgroup.mem_sup_right (mem_zpowers s), ?_⟩
      intro b hb
      obtain ⟨q, hq, hb' | hb'⟩ := (mem_sup_zpowers_sq hs hN).1 hb
      · right; rw [hb']; exact hq
      · left
        have : q * s * s = q * (s * s) := by rw [mul_assoc]
        rw [hb', this]
        exact N.mul_mem hq hs
    have hne : N.relIndex (N ⊔ zpowers s) ≠ 1 := by
      intro h1
      rw [relIndex_eq_one] at h1
      exact hsN (h1 (Subgroup.mem_sup_right (mem_zpowers s)))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := relIndex_mul_card N (N ⊔ zpowers s)
  rw [inf_of_le_left hle, hrel] at this
  exact this.symm

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
