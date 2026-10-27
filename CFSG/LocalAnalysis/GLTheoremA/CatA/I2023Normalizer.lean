module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCoreOf_le_normalizer_of_component {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) :
    GLAPPrimeCoreOf p X ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hg' : g ∈ (GLAPPrimeCore p ↥X).map X.subtype := hg
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hg'
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  have hπy : π y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  have hgX : g ∈ X := by rw [← hyg]; exact y.2
  have hyX : (y : G) = g := hyg
  have hconj : ∀ w : ↥X, π (y⁻¹ * w * y) = π w := by
    intro w
    simp [hπy]
  have hX : GLBConj g X = X :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hgX)
  have hcomp : GLAPComponent p X (GLBConj g L) := by
    have h := glaPComponent_gLBConj hL g
    rw [hX] at h
    exact h
  have hLX : L ≤ X := hL.1
  have hbar : barX p X (GLBConj g L) = barX p X L := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      have hw' : (w : G) ∈ GLBConj g L := (Subgroup.mem_subgroupOf).1 hw
      have hl : g * (w : G) * g⁻¹ ∈ L := mem_gLBConj.1 hw'
      have hlX : g * (w : G) * g⁻¹ ∈ X := hLX hl
      have hwl : w = y⁻¹ * (⟨g * (w : G) * g⁻¹, hlX⟩ : ↥X) * y := by
        apply Subtype.ext
        simp [hyX]
        group
      refine Subgroup.mem_map.2 ⟨⟨g * (w : G) * g⁻¹, hlX⟩, ?_, ?_⟩
      · exact (Subgroup.mem_subgroupOf).2 hl
      · show π ⟨g * (w : G) * g⁻¹, hlX⟩ = π w
        rw [← hconj ⟨g * (w : G) * g⁻¹, hlX⟩]
        exact congrArg π hwl.symm
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      have hw' : (w : G) ∈ L := (Subgroup.mem_subgroupOf).1 hw
      have hw'' : y⁻¹ * w * y ∈ (GLBConj g L).subgroupOf X := by
        rw [Subgroup.mem_subgroupOf, mem_gLBConj]
        have e : g * ((y⁻¹ * w * y : ↥X) : G) * g⁻¹ = (w : G) := by
          simp [hyX]
          group
        rw [e]
        exact hw'
      refine Subgroup.mem_map.2 ⟨y⁻¹ * w * y, hw'', ?_⟩
      exact hconj w
  have hfin : L = GLBConj g L :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_uniqueAux hL hcomp hbar.symm
  exact mem_normalizer_iff_gLBConj_eq.2 hfin.symm

end CFSG.LocalAnalysis.GLTheoremA

end
