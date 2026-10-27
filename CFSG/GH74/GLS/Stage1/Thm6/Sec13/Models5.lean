module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models4
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

theorem card_multiplicative_zmod (m : ℕ) [NeZero m] : Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_E24 : Nat.card E24 = 4 ^ 2 := by
  rw [Nat.card_fun, card_multiplicative_zmod]
  simp

theorem card_Z2n2 (n : ℕ) : Nat.card (Z2n2 n) = 4 ^ n := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [Nat.card_prod, card_multiplicative_zmod]
  rw [← mul_pow]
  norm_num

theorem comm_of_equiv_comm {P M : Type*} [Group P] [CommGroup M] (e : P ≃* M) (a b : P) :
    a * b = b * a := by
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

theorem transport_nonabelian {P M : Type*} [Group P] [Group M] (e : P ≃* M)
    (hcard : Nat.card M = 64) (hcomm : ∀ a b c : M, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hcen : ∀ Z : Subgroup M, (∀ z ∈ Z, ∀ c : M, z * c = c * z) → Nat.card Z ≤ 4) :
    Nat.card P = 64 ∧ (∀ a b c : P, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      ∀ Z : Subgroup P, (∀ z ∈ Z, ∀ c : P, z * c = c * z) → Nat.card Z ≤ 4 := by
  refine ⟨by rw [Nat.card_congr e.toEquiv]; exact hcard, ?_, ?_⟩
  · intro a b c
    apply e.injective
    rw [map_mul, map_mul, map_commutatorElement]
    exact hcomm _ _ _
  · intro Z hZ
    have hmap : Nat.card (Z.map e.toMonoidHom) ≤ 4 := by
      apply hcen
      rintro _ ⟨z, hz, rfl⟩ c
      obtain ⟨c', rfl⟩ := e.surjective c
      show e z * e c' = e c' * e z
      rw [← map_mul, ← map_mul, hZ z hz c']
    rwa [Subgroup.card_map_of_injective e.injective] at hmap

theorem IsYGroup.card_pow4 {P : Type*} [Group P] (h : IsYGroup P) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card P = 4 ^ n := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact ⟨2, by norm_num, by rw [Nat.card_congr e.toEquiv, card_E24]⟩
  · refine ⟨3, by norm_num, ?_⟩
    rw [Nat.card_congr e.toEquiv, UT3.card_eq]
    have := GaloisField.card 2 2 (by norm_num)
    simp at this
    rw [this]
  · refine ⟨3, by norm_num, ?_⟩
    rw [Nat.card_congr e.toEquiv, card_SylSU34]; norm_num
  · exact ⟨n, hn, by rw [Nat.card_congr e.toEquiv, card_Z2n2]⟩

theorem IsYGroup.nonabelian_facts {P : Type*} [Group P] (h : IsYGroup P)
    (hna : ∃ a b : P, a * b ≠ b * a) :
    Nat.card P = 64 ∧ (∀ a b c : P, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      ∀ Z : Subgroup P, (∀ z ∈ Z, ∀ c : P, z * c = c * z) → Nat.card Z ≤ 4 := by
  obtain ⟨a, b, hab⟩ := hna
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact absurd (comm_of_equiv_comm e a b) hab
  · apply transport_nonabelian e
    · rw [UT3.card_eq]
      have := GaloisField.card 2 2 (by norm_num)
      simp at this
      rw [this]; norm_num
    · exact UT3.comm_central
    · exact UT3_gf4_central_card
  · apply transport_nonabelian e card_SylSU34 SylSU34_comm_central SylSU34_central_card
  · exact absurd (comm_of_equiv_comm e a b) hab

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
