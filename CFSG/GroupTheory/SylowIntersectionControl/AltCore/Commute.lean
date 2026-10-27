module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.GroupTheory.AltCore

open Subgroup CFSG.ABGLocalTools CFSG.ClassicalInvolution.GlaubermanAut

variable {G : Type*} [Group G] [Finite G]

private theorem lt_inf_of_isSylowOf {p : ℕ} [Fact p.Prime] {H K N S : Subgroup G}
    (hS : IsSylowOf p S N) (hHS : H ≤ S) (hHK : H ≤ K) (hKN : K ≤ N)
    (hnK : N ≤ normalizer (K : Set G)) (hp : p ∣ H.relIndex K) : H < S ⊓ K := by
  have hSK : IsSylowOf p (S ⊓ K) K := hS.inf_of_le_normalizer hKN hnK
  refine lt_of_le_of_ne (le_inf hHS hHK) fun heq => ?_
  exact (isSylowOf_iff.mp hSK).2.2 (heq ▸ hp)

omit [Finite G] in
private theorem le_normalizer_of_commute {H K₁ K₂ B : Subgroup G} (hHB : H ≤ B) (hBK : B ≤ K₂)
    (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y * x⁻¹ * y⁻¹ ∈ H) : K₁ ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    have h := B.mul_mem (hHB (hc a ha b (hBK hb))) hb
    simpa [mul_assoc] using h
  · intro hb
    have h := B.mul_mem (hHB (hc a⁻¹ (K₁.inv_mem ha) _ (hBK hb))) hb
    simpa [mul_assoc] using h

theorem not_isPIsolatedOver_of_commute {H N K₁ K₂ : Subgroup G} (hH : IsPGroup 2 H)
    (hHN : H ≤ N) (hN : N ≤ normalizer (H : Set G)) (hK₁ : H ≤ K₁) (hK₂ : H ≤ K₂)
    (hK₁N : K₁ ≤ N) (hK₂N : K₂ ≤ N) (hn₁ : N ≤ normalizer (K₁ : Set G))
    (hn₂ : N ≤ normalizer (K₂ : Set G)) (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y * x⁻¹ * y⁻¹ ∈ H)
    (h₁ : 2 ∣ H.relIndex K₁) (h₂ : 2 ∣ H.relIndex K₂) : ¬ IsPIsolatedOver 2 N H := by
  rintro ⟨S, T, hS, hT, hnot⟩
  refine hnot ?_
  have hHS : H ≤ S := isSylowOf_le_of_le_normalizer hS hH hHN hN
  have hHT : H ≤ T := isSylowOf_le_of_le_normalizer hT hH hHN hN
  have hA : H < S ⊓ K₁ := lt_inf_of_isSylowOf hS hHS hK₁ hK₁N hn₁ h₁
  have hB : H < T ⊓ K₂ := lt_inf_of_isSylowOf hT hHT hK₂ hK₂N hn₂ h₂
  have hAn : S ⊓ K₁ ≤ normalizer ((T ⊓ K₂ : Subgroup G) : Set G) :=
    inf_le_right.trans (le_normalizer_of_commute hB.le inf_le_right hc)
  have hP : IsPGroup 2 ((S ⊓ K₁) ⊔ (T ⊓ K₂) : Subgroup G) :=
    hS.isPGroup.to_inf_left.to_sup_of_normal_right' hT.isPGroup.to_inf_left hAn
  obtain ⟨U, hU, hUN⟩ := exists_isSylowOf_ge hP
    (sup_le (inf_le_right.trans hK₁N) (inf_le_right.trans hK₂N))
  exact (Relation.EqvGen.rel _ _ ⟨hS, hUN,
      lt_of_lt_of_le hA (le_inf inf_le_left (le_sup_left.trans hU))⟩).trans _ _ _
    (Relation.EqvGen.rel _ _ ⟨hUN, hT,
      lt_of_lt_of_le hB (le_inf (le_sup_right.trans hU) inf_le_left)⟩)

end CFSG.GroupTheory.AltCore
