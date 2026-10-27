module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Subgroup

theorem eq_of_abelian_index_three {R : Type*} [Group R] [Finite R] {T A Z₀ : Subgroup R}
    [T.Normal] (hTi : T.index = 3) (hAi : A.index = 3)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hZ : ∀ r : R, r ∉ T → ∀ d ∈ T, r * d = d * r → d ∈ Z₀)
    (hcard : 3 * Nat.card Z₀ < Nat.card T) : A = T := by
  by_contra hne
  have hAT : ¬ A ≤ T := fun hle => hne (by
    have h1 := relIndex_mul_index hle
    rw [hTi, hAi] at h1
    have : A.relIndex T = 1 := by omega
    exact le_antisymm hle (relIndex_eq_one.mp this))
  have hsup : T ⊔ A = ⊤ := by
    have h1 := relIndex_mul_index (le_sup_left : T ≤ T ⊔ A)
    rw [hTi] at h1
    have hd : (T ⊔ A).index ∣ 3 := ⟨T.relIndex (T ⊔ A), by rw [mul_comm]; exact h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact index_eq_one.mp h
    · exfalso
      have : T.relIndex (T ⊔ A) = 1 := by rw [h] at h1; omega
      exact hAT (le_trans le_sup_right (relIndex_eq_one.mp this))
  have hrel : T.relIndex A = 3 := by
    have := relIndex_sup_left (H := A) (K := T)
    rw [hsup, relIndex_top_right, hTi] at this
    exact this.symm
  obtain ⟨r, hrA, hrT⟩ := Set.not_subset.mp hAT
  have hle : (T.subgroupOf A).map A.subtype ≤ Z₀ := by
    rintro _ ⟨d, hd, rfl⟩
    exact hZ r hrT d (Subgroup.mem_subgroupOf.mp hd) (hAc r hrA d d.2)
  have hc1 : Nat.card (T.subgroupOf A) * 3 = Nat.card A := by
    have := card_mul_index (T.subgroupOf A)
    rwa [show (T.subgroupOf A).index = 3 from hrel] at this
  have hcAT : Nat.card A = Nat.card T := by
    have h1 := card_mul_index A
    have h2 := card_mul_index T
    rw [hAi] at h1
    rw [hTi] at h2
    omega
  have hcle : Nat.card ((T.subgroupOf A).map A.subtype) ≤ Nat.card Z₀ :=
    Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective A.subtype_injective] at hcle
  omega

end CFSG.HardMathSupport.Curtis.Coordinator
