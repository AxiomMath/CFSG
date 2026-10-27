module

public import CFSG.ClassicalInvolution.Asc77.AscT7MK
public import CFSG.ClassicalInvolution.Asc77.AscT7MJ

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy

section Layers

variable {X P : Type} [Group X] [Finite X] [Group P] {θ : X →* MulAut P} {ι : P →* X}

theorem alphaOf_klein_of_layers (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p)
    (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1) {y z : X} (hz2 : z * z = 1) (hy2 : y * y = 1)
    (hzy : z * y = y * z) (hz1 : z ≠ 1) (hy1 : y ≠ 1) (hzy1 : z * y ≠ 1) {Q₁ Q₂ : Subgroup P}
    (hfix₁ : ∀ q ∈ Q₁, θ y q = q) (hnorm₁ : ∀ g : P, θ y g = g → ∀ q ∈ Q₁, g * q * g⁻¹ ∈ Q₁)
    (hperf₁ : Q₁ ≤ ⁅Q₁, Q₁⁆)
    (hgen₁ : ∃ 𝓗 : Set (Subgroup P), (∀ H ∈ 𝓗, H ≤ Q₁ ∧ CFSG.Open.IsQuasisimple ↥H ∧
      ∀ p ∈ Q₁, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ Q₁ ≤ ⨆ H ∈ 𝓗, H)
    (hfix₂ : ∀ q ∈ Q₂, θ (z * y) q = q)
    (hnorm₂ : ∀ g : P, θ (z * y) g = g → ∀ q ∈ Q₂, g * q * g⁻¹ ∈ Q₂)
    (hperf₂ : Q₂ ≤ ⁅Q₂, Q₂⁆)
    (hgen₂ : ∃ 𝓗 : Set (Subgroup P), (∀ H ∈ 𝓗, H ≤ Q₂ ∧ CFSG.Open.IsQuasisimple ↥H ∧
      ∀ p ∈ Q₂, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ Q₂ ≤ ⨆ H ∈ 𝓗, H)
    (hz₁ : z ∈ Q₁.map ι) (hz₂ : z ∈ Q₂.map ι)
    (hN : ∀ n ∈ involutionOddCore z, n * y = y * n) (hsup : Q₁ ⊔ Q₂ = ⊤) :
    alphaOf (Subgroup.closure ({z, y} : Set X)) = ⊥ := by
  have : ι.range.Normal := range_normal hθ hι
  have d₁ : LayerData ι.range (Subgroup.closure ({z, y} : Set X)) y (Q₁.map ι) := by
    refine layerData_of_fix hθ hι hZ (a := y) (Q := Q₁) hfix₁ hnorm₁ hperf₁ hgen₁ ?_
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_right hz₁
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have d₂ : LayerData ι.range (Subgroup.closure ({z, y} : Set X)) (z * y) (Q₂.map ι) := by
    refine layerData_of_fix hθ hι hZ (a := z * y) (Q := Q₂) hfix₂ hnorm₂ hperf₂ hgen₂ ?_
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_right hz₂
    · have hyz : z * (z * y) = y := by rw [← mul_assoc, hz2, one_mul]
      have hmem := Subgroup.mul_mem (Subgroup.zpowers (z * y) ⊔ Q₂.map ι)
        (Subgroup.mem_sup_right hz₂) (Subgroup.mem_sup_left (Subgroup.mem_zpowers (z * y)))
      rw [hyz] at hmem
      rw [hg]
      exact hmem
  refine alphaOf_klein_outer ι.range hz2 hy2 hzy hz1 hy1 hzy1 d₁ d₂ hN ?_
  intro x _ h₁ h₂
  exact eq_one_of_fix_of_sup_eq_top hθ hι hZ hsup h₁ h₂

end Layers

end CFSG.ClassicalInvolution.ModelFacts.Orth15
