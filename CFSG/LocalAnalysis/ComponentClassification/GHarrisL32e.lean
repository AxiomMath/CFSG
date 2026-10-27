module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32d

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev a1l : G := D.toG (SE.invRep 2)

abbrev a3a4 : G := D.toG (SE.invRep 3)

omit [Finite G] in
theorem card_C_a1l : Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({D.a1l} : Set G)) = 128 := by
  have h := D.card_centralizer_invRep_G 2
  rw [show SE.invRepCent 2 = 128 from rfl] at h
  exact h

omit [Finite G] in
theorem card_C_a3a4 : Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G)) = 64 := by
  have h := D.card_centralizer_invRep_G 3
  rw [show SE.invRepCent 3 = 64 from rfl] at h
  exact h

omit [Finite G] in
theorem toG_invRep_mul_self (i : Fin 9) : D.toG (SE.invRep i) * D.toG (SE.invRep i) = 1 := by
  rw [← map_mul, show SE.invRep i * SE.invRep i = 1 by revert i; decide, map_one]

omit [Finite G] in
theorem toG_invRep_ne_one (i : Fin 9) : D.toG (SE.invRep i) ≠ 1 := by
  rw [Ne, D.toG_eq_one_iff]
  revert i
  decide

theorem not_conj_x_a1l :
    ¬ ∃ g : G, g⁻¹ * D.x * g = D.a1l := by
  classical
  rintro ⟨g, hg⟩
  have hxz := D.not_conj_x_z
  have hxt := D.not_conj_x_t
  have ha : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.a1l} : Set G))
      (centralizer ({D.a1l} : Set G)) := by
    refine D.isSylowOf_of_classes (D.toG_mem _) (D.toG_invRep_mul_self 2) (D.toG_invRep_ne_one 2)
      fun i ⟨h, hh⟩ => ?_
    rw [D.card_C_a1l]
    by_cases hi0 : i = 0
    · subst hi0
      rw [SE.invRep_zero] at hh
      exact absurd ⟨g * h, by
        rw [show (g * h)⁻¹ * D.x * (g * h) = h⁻¹ * (g⁻¹ * D.x * g) * h by group, hg, hh]⟩ hxz
    by_cases hi1 : i = 1
    · subst hi1
      exact absurd ⟨g * h, by
        rw [show (g * h)⁻¹ * D.x * (g * h) = h⁻¹ * (g⁻¹ * D.x * g) * h by group, hg, hh]⟩ hxt
    exact SE.invRepCent_le_of_two_le i hi0 hi1
  obtain ⟨g₁, -, hX⟩ := exists_conj_extremal D.S.isPGroup' ha
    (show g⁻¹⁻¹ * D.a1l * g⁻¹ = D.x by rw [← hg]; group)
  have hmem : ∀ c₀ : {c : SE // c * SE.gen 6 = SE.gen 6 * c ∧ c * c = 1 ∧ c ≠ 1},
      g₁⁻¹ * D.toG c₀.1 * g₁ ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a1l} : Set G) := by
    intro c₀
    exact hX _ (mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, c₀.2.1])⟩)
  choose f hf using fun c₀ => D.exists_toG (mem_inf.mp (hmem c₀)).1
  let F : {c : SE // c * SE.gen 6 = SE.gen 6 * c ∧ c * c = 1 ∧ c ≠ 1} →
      {c : SE // c * SE.invRep 2 = SE.invRep 2 * c ∧ c * c = 1 ∧ c ≠ 1} := fun c₀ => ⟨f c₀, by
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp (hmem c₀)).2
    rw [← hf c₀, ← map_mul, ← map_mul] at h1
    refine ⟨D.toG_injective h1, D.toG_injective ?_, fun h => c₀.2.2.2 (D.toG_injective ?_)⟩
    · rw [map_mul, hf c₀, map_one,
        show g₁⁻¹ * D.toG c₀.1 * g₁ * (g₁⁻¹ * D.toG c₀.1 * g₁) = g₁⁻¹ * D.toG (c₀.1 * c₀.1) * g₁ by
          rw [map_mul]; group, c₀.2.2.1, map_one]
      group
    · have h2 := hf c₀
      rw [h, map_one] at h2
      rw [map_one]
      calc D.toG c₀.1 = g₁ * (g₁⁻¹ * D.toG c₀.1 * g₁) * g₁⁻¹ := by group
        _ = 1 := by rw [← h2]; group⟩
  have hF : Function.Injective F := by
    intro c₁ c₂ h12
    have h2 := congrArg D.toG (congrArg Subtype.val h12 : f c₁ = f c₂)
    rw [hf, hf] at h2
    have h3 : D.toG c₁.1 = D.toG c₂.1 := by
      have := congrArg (fun y => g₁ * y * g₁⁻¹) h2
      simpa [mul_assoc] using this
    exact Subtype.ext (D.toG_injective h3)
  have hcard := Fintype.card_le_of_injective F hF
  rw [Fintype.card_subtype, Fintype.card_subtype, SE.card_inv_centralizer_x,
    SE.card_inv_centralizer_a1l] at hcard
  omega

end GHSylow

end CFSG.ComponentClassification.GHarris
