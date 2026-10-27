module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32b
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31d

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem pow_four_cases_S {c : G} (hc : c ∈ (D.S : Subgroup G)) :
    c ^ 4 = 1 ∨ c ^ 4 = D.z ∨ c ^ 4 = D.t ∨ c ^ 4 = D.t * D.z := by
  obtain ⟨c₀, rfl⟩ := D.exists_toG hc
  rw [← map_pow]
  rcases SE.pow_four_cases c₀ with h | h | h | h <;> rw [h]
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

omit [Finite G] in
theorem x_ne_z : D.x ≠ D.z := fun h => absurd (D.toG_injective h) (by decide)

omit [Finite G] in
theorem comm_z_of_mem_X {c : G} (hc : c ∈ D.X) : c * D.z = D.z * c :=
  mem_centralizer_singleton_iff.mp (D.S_le_centralizer_z (mem_inf.mp hc).1)

theorem isSylowOf_z : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({D.z} : Set G))
    (centralizer ({D.z} : Set G)) :=
  isSylowOf_inf_centralizer_of_le (isSylowOf_top D.S) D.S_le_centralizer_z

theorem not_conj_x_z :
    ¬ ∃ g : G, g⁻¹ * D.x * g = D.z := by
  rintro ⟨g, hg⟩
  obtain ⟨g₁, hg₁, hX⟩ := exists_conj_extremal D.S.isPGroup' D.isSylowOf_z
    (show g⁻¹⁻¹ * D.z * g⁻¹ = D.x by rw [← hg]; group)
  have hXS : ∀ c ∈ D.X, g₁⁻¹ * c * g₁ ∈ (D.S : Subgroup G) := fun c hc => (mem_inf.mp (hX c hc)).1
  set w := g₁⁻¹ * D.z * g₁ with hw
  have hw4 : w = (g₁⁻¹ * D.ay * g₁) ^ 4 := by rw [conj_pow_inv, D.ay_pow_four]
  have hw1 : w ≠ 1 := fun h => D.z_ne_one (by
    calc D.z = g₁ * w * g₁⁻¹ := by rw [hw]; group
      _ = 1 := by rw [h]; group)
  have hwz : w ≠ D.z := fun h => D.x_ne_z (by
    calc D.x = g₁ * (g₁⁻¹ * D.x * g₁) * g₁⁻¹ := by group
      _ = g₁ * w * g₁⁻¹ := by rw [hg₁, h]
      _ = D.z := by rw [hw]; group)
  obtain ⟨g₂, hg₂z, hg₂x, hg₂X⟩ : ∃ g₂ : G, g₂⁻¹ * D.z * g₂ = D.t ∧ g₂⁻¹ * D.x * g₂ = D.z ∧
      ∀ c ∈ D.X, g₂⁻¹ * c * g₂ ∈ (D.S : Subgroup G) := by
    rcases D.pow_four_cases_S (hXS _ D.ay_mem_X) with h | h | h | h <;> rw [← hw4] at h
    · exact absurd h hw1
    · exact absurd h hwz
    · exact ⟨g₁, h, hg₁, hXS⟩
    · set y := D.toG (SE.gen 7)
      have hyS : y ∈ (D.S : Subgroup G) := D.toG_mem _
      refine ⟨g₁ * y, ?_, ?_, fun c hc => ?_⟩
      · rw [show (g₁ * y)⁻¹ * D.z * (g₁ * y) = y⁻¹ * w * y by rw [hw]; group, h,
          show y⁻¹ * (D.t * D.z) * y = (y⁻¹ * D.t * y) * (y⁻¹ * D.z * y) by group, D.conj_y_t,
          D.conj_z_S hyS, mul_assoc, D.z_mul_z, mul_one]
      · rw [show (g₁ * y)⁻¹ * D.x * (g₁ * y) = y⁻¹ * (g₁⁻¹ * D.x * g₁) * y by group, hg₁,
          D.conj_z_S hyS]
      · rw [show (g₁ * y)⁻¹ * c * (g₁ * y) = y⁻¹ * (g₁⁻¹ * c * g₁) * y by group]
        exact mul_mem (mul_mem (inv_mem hyS) (hXS c hc)) hyS
  obtain ⟨u, huN, huz, hut⟩ := D.exists_swap_z_t ⟨g₂, hg₂z⟩
  refine D.false_of_conj_X_Ct (h := g₂ * u) (fun c hc => ?_) ?_
  · have hcC : g₂⁻¹ * c * g₂ ∈ D.Ct := by
      refine mem_inf.mpr ⟨hg₂X c hc, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hg₂z]
      calc g₂⁻¹ * c * g₂ * (g₂⁻¹ * D.z * g₂) = g₂⁻¹ * (c * D.z) * g₂ := by group
        _ = g₂⁻¹ * (D.z * c) * g₂ := by rw [D.comm_z_of_mem_X hc]
        _ = g₂⁻¹ * D.z * g₂ * (g₂⁻¹ * c * g₂) := by group
    rw [show (g₂ * u)⁻¹ * c * (g₂ * u) = u⁻¹ * (g₂⁻¹ * c * g₂) * u by group]
    exact conj_mem_of_mem_normalizer huN hcC
  · rw [show (g₂ * u)⁻¹ * D.z * (g₂ * u) = u⁻¹ * (g₂⁻¹ * D.z * g₂) * u by group, hg₂z, hut]

end GHSylow

end CFSG.ComponentClassification.GHarris
