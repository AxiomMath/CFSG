module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G]

theorem gLBConj_glaDelta_le (p : ℕ) (g : G) (D : Subgroup G) :
    GLBConj g (GLADelta p D) ≤ GLADelta p (GLBConj g D) := by
  intro y hy
  rw [mem_gLBConj] at hy
  simp only [GLADelta, Subgroup.mem_iInf] at hy ⊢
  intro d hd hd1
  have hgd : g * d * g⁻¹ ∈ D := mem_gLBConj.mp hd
  have hgd1 : g * d * g⁻¹ ≠ 1 := by
    intro h
    apply hd1
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h1 : GLBConj g (Subgroup.centralizer ({g * d * g⁻¹} : Set G)) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [← centralizer_singleton_gLBConj, show g⁻¹ * (g * d * g⁻¹) * g = d by group]
  have h2 := hy (g * d * g⁻¹) hgd hgd1
  rw [← h1, glaPPrimeCoreOf_gLBConj, mem_gLBConj]
  exact h2

theorem gLBConj_glaDelta_le_of_mem_normalizer {p : ℕ} {g : G} {D : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    GLBConj g (GLADelta p D) ≤ GLADelta p D := by
  intro y hy
  have h := gLBConj_glaDelta_le p g D hy
  rwa [mem_normalizer_iff_gLBConj_eq.mp hg] at h

theorem normalizer_le_normalizer_glaDelta (p : ℕ) (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (GLADelta p D : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (D : Set G), ∀ x ∈ GLADelta p D,
      g * x * g⁻¹ ∈ GLADelta p D := by
    intro g hg x hx
    have hz : g * x * g⁻¹ ∈ GLBConj g⁻¹ (GLADelta p D) := by
      rw [mem_gLBConj, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]
      exact hx
    exact gLBConj_glaDelta_le_of_mem_normalizer (inv_mem hg) hz
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have h := key g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

end CFSG.HardMathSupport.Solomon.Proving

end
