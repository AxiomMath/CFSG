module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoFusionSteps

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoPilot


theorem exists_conj_eq_rep_E6_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (x : adjointGroup .E6 K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ c : adjointGroup .E6 K, c * x * c⁻¹ = uE6Two 0 ∨ c * x * c⁻¹ = uE6Two 0 * uE6Two 3 ∨
      c * x * c⁻¹ = uE6Two 0 * uE6Two 2 * uE6Two 3 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c₁, hc₁⟩ := exists_conj_mem_range_psiHom h2 hK hx3
  obtain ⟨y, hy⟩ := hc₁
  have hy3 : psiHom K h2 y ^ 3 = 1 := by
    rw [hy, conj_pow, hx3]
    group
  obtain ⟨c₂, w, hc₂⟩ := exists_conj_torus_of_psiHom h2 y hy3
  have hw : w ≠ 0 := by
    rintro rfl
    apply hx1
    have h1 : c₂ * (c₁ * x * c₁⁻¹) * c₂⁻¹ = 1 := by
      rw [← hy, hc₂]
      exact map_one _
    calc x = c₁⁻¹ * c₂⁻¹ * (c₂ * (c₁ * x * c₁⁻¹) * c₂⁻¹) * c₂ * c₁ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨c₃, r, hr, hc₃⟩ := exists_conj_bReps h2 hw
  refine ⟨c₃ * c₂ * c₁, ?_⟩
  have e : c₃ * c₂ * c₁ * x * (c₃ * c₂ * c₁)⁻¹ = torusE6Two h2 (.ofAdd r) := by
    rw [← hc₃, ← hc₂, hy]
    group
  rw [e]
  simp only [bReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl (torus_bRep₀ h2)
  · exact Or.inr (Or.inl (torus_bRep₁ h2))
  · exact Or.inr (Or.inr (torus_bRep₂ h2))

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
