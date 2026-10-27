module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma conjIn_trans {M : Subgroup G} {a b : G} (ha : a ∈ conjIn M t) {m : G} (hm : m ∈ M)
    (hb : m * a * m⁻¹ = b) : b ∈ conjIn M t := by
  obtain ⟨k, hk, rfl⟩ := ha
  exact ⟨m * k, M.mul_mem hm hk, by rw [← hb]; group⟩

theorem tG_inf_X_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h48 : Lemma4_8Concl t x₁ x₂ rho tau)
    (h49 : Lemma4_9Concl t S x₁ x₂ tau) :
    {u : G | (∃ g : G, g * t * g⁻¹ = u) ∧ u ∈ ctxX t tau x₁ x₂} =
      conjIn (ctxM t tau x₁ x₂) t := by
  ext u
  constructor
  · rintro ⟨⟨g, hg⟩, huX⟩
    have htF : ∀ f ∈ (fourGrp x₁ x₂ : Set G), t * f ∈ conjIn (ctxM t tau x₁ x₂) t := by
      intro f hf
      have hmem : t * f ∈ t • (fourGrp x₁ x₂ : Set G) := ⟨f, hf, rfl⟩
      rcases h49.2 with h1 | h1 | h1 | h1 <;> rw [h1]
      · exact hmem
      · exact Or.inl hmem
      · exact Or.inl hmem
      · exact Or.inl (Or.inl hmem)
    rcases mem_ctxX_cases h h44 huX with hF | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩
    · exact absurd hg (tG_inf_four_of_ctx h g u hF)
    · exact htF f hf
    ·
      obtain ⟨⟨m, hm, hmu⟩, -⟩ := tau_mul_mem_conjIn h h43 h44 hf
      have hconj : ∃ g' : G, g' * tau * g'⁻¹ = t := by
        refine ⟨g⁻¹ * m, ?_⟩
        calc g⁻¹ * m * tau * (g⁻¹ * m)⁻¹ = g⁻¹ * (m * tau * m⁻¹) * g := by group
          _ = g⁻¹ * (tau * f) * g := by rw [hmu]
          _ = t := by
            have : tau * f = g * t * g⁻¹ := hg.symm
            rw [this]; group
      obtain ⟨g'', hg''M, hg''t, -⟩ := h48.1.mp hconj
      have hτ : tau ∈ conjIn (ctxM t tau x₁ x₂) t :=
        ⟨g''⁻¹, (ctxM t tau x₁ x₂).inv_mem (Subgroup.mem_inf.mp hg''M).1, by
          calc g''⁻¹ * t * g''⁻¹⁻¹ = g''⁻¹ * (g'' * tau * g''⁻¹) * g'' := by rw [hg''t]; group
            _ = tau := by group⟩
      exact conjIn_trans hτ hm hmu
    ·
      obtain ⟨-, ⟨m, hm, hmu⟩⟩ := tau_mul_mem_conjIn h h43 h44 hf
      have hconj : ∃ g' : G, g' * (t * tau) * g'⁻¹ = t := by
        refine ⟨g⁻¹ * m, ?_⟩
        calc g⁻¹ * m * (t * tau) * (g⁻¹ * m)⁻¹ = g⁻¹ * (m * (t * tau) * m⁻¹) * g := by group
          _ = g⁻¹ * (t * tau * f) * g := by rw [hmu]
          _ = t := by
            have : t * tau * f = g * t * g⁻¹ := hg.symm
            rw [this]; group
      obtain ⟨g'', hg''M, hg''t, -⟩ := h48.2.mp hconj
      have hτ : t * tau ∈ conjIn (ctxM t tau x₁ x₂) t :=
        ⟨g''⁻¹, (ctxM t tau x₁ x₂).inv_mem (Subgroup.mem_inf.mp hg''M).1, by
          calc g''⁻¹ * t * g''⁻¹⁻¹ = g''⁻¹ * (g'' * (t * tau) * g''⁻¹) * g'' := by
                rw [hg''t]; group
            _ = t * tau := by group⟩
      exact conjIn_trans hτ hm hmu
  · intro hu
    refine ⟨?_, conjIn_ctxM_subset_ctxX t tau x₁ x₂ hu⟩
    obtain ⟨k, -, rfl⟩ := hu
    exact ⟨k, rfl⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
