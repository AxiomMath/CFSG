module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUOrb

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

@[expose] def ModelZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    Sect7Hyps G L f s y S₀ n → ∀ (C : ECoord G), Sect8Hyp C f n S₀ →
      ∃ r v₀ w₀ ρ e₀ : G,
        r ∈ SAU.M0 C f ∧ r ^ 3 = 1 ∧ r ≠ 1 ∧
        v₀ ∈ SAU.M0 C f ∧ v₀ ^ 7 = 1 ∧
        (∀ x ∈ C.E, x ∈ L → v₀ * x * v₀⁻¹ = x → x = 1 ∨ x = f ^ 2) ∧
        e₀ ∈ C.E ∧ r * e₀ = e₀ * r ∧ e₀ * e₀ ≠ 1 ∧ e₀ * e₀ ≠ f ^ 2 ∧
        SAU.IsW C f L y w₀ ∧ w₀ * w₀ = 1 ∧ Cl16 C f w₀ ∧ r * w₀ = w₀ * r ∧
        ρ ^ 3 = 1 ∧ ρ * f ^ 2 = f ^ 2 * ρ ∧ ρ ∉ zpowers r ∧ ρ * r = r * ρ ∧ ρ * w₀ = w₀ * ρ

namespace ECoord

theorem mat_eq_neg_one_of_inv {G : Type} [Group G] {C : ECoord G} {u : G}
    (hu : u ∈ normalizer (C.E : Set G)) (h : ∀ e ∈ C.E, u * e * u⁻¹ = e⁻¹) :
    C.mat u = -1 := by
  have key : ∀ v : V4, C.mat u *ᵥ v = -v := by
    intro v
    apply C.elt_injective
    rw [← C.conj_elt hu, h _ (C.elt_mem v), C.elt_neg]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  by_cases hij : i = j <;> simp_all

end ECoord

section Cl16

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}
  {C : ECoord G}

theorem Cl16.of_coset {w₀ u e : G} (hcl : Cl16 C f w₀) (he : e ∈ SAU.OmegaE C)
    (hw₀ : w₀ = u * e) : Cl16 C f u := by
  intro m hmc hmn
  obtain ⟨ε, hεE, hεε, hε⟩ := hcl m hmc hmn
  have hΩ : m * e * m⁻¹ ∈ SAU.OmegaE C := by
    refine ⟨(mem_normalizer_iff.1 hmn e).1 he.1, ?_⟩
    calc m * e * m⁻¹ * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = 1 := by rw [he.2]; group
  have hε' : ε ∈ SAU.OmegaE C := ⟨hεE, hεε⟩
  have hmem : e * ε * (m * e * m⁻¹)⁻¹ ∈ SAU.OmegaE C :=
    mul_mem (mul_mem he hε') (inv_mem hΩ)
  refine ⟨_, hmem.1, hmem.2, ?_⟩
  have hu : u = w₀ * e⁻¹ := by rw [hw₀]; group
  have h1 : m * u * m⁻¹ = (m * w₀ * m⁻¹) * (m * e * m⁻¹)⁻¹ := by rw [hu]; group
  rw [h1, hε, hw₀]
  group

theorem Cl16.of_conj {w m₁ : G} (hm₁ : m₁ ∈ SAU.M0 C f) (hcl : Cl16 C f (m₁ * w * m₁⁻¹)) :
    Cl16 C f w := by
  intro m hmc hmn
  have hm' : m₁ * m * m₁⁻¹ ∈ SAU.M0 C f :=
    mul_mem (mul_mem hm₁ (SAU.mem_M0.2 ⟨hmc, hmn⟩)) (inv_mem hm₁)
  obtain ⟨ε, hεE, hεε, hε⟩ := hcl _ (SAU.mem_M0.1 hm').1 (SAU.mem_M0.1 hm').2
  have hm₁n := (SAU.mem_M0.1 hm₁).2
  refine ⟨m₁⁻¹ * ε * m₁, ?_, ?_, ?_⟩
  · have := (mem_normalizer_iff.1 (inv_mem hm₁n) ε).1 hεE
    simpa using this
  · calc m₁⁻¹ * ε * m₁ * (m₁⁻¹ * ε * m₁) = m₁⁻¹ * (ε * ε) * m₁ := by group
      _ = 1 := by rw [hεε]; group
  · have h1 : m₁ * (m * w * m⁻¹) * m₁⁻¹ = m₁ * w * m₁⁻¹ * ε := by
      rw [← hε]
      group
    calc m * w * m⁻¹ = m₁⁻¹ * (m₁ * (m * w * m⁻¹) * m₁⁻¹) * m₁ := by group
      _ = m₁⁻¹ * (m₁ * w * m₁⁻¹ * ε) * m₁ := by rw [h1]
      _ = w * (m₁⁻¹ * ε * m₁) := by group

end Cl16

end CFSG.EvenSporadicStandard.TwoHS
