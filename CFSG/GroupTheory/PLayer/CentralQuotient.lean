module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral

public section

namespace CFSG

open CFSG.Open

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

theorem glaPComponent_map_bijective_of_ker_le_center {p : ℕ} (hp : p.Prime) (f : G →* G')
    {X : Subgroup G} (hc : ∀ y ∈ X ⊓ f.ker, ∀ x ∈ X, x * y = y * x) :
    (∀ J : Subgroup G, GLAPComponent p X J → GLAPComponent p (X.map f) (J.map f)) ∧
      (∀ J' : Subgroup G', GLAPComponent p (X.map f) J' →
        ∃ J : Subgroup G, GLAPComponent p X J ∧ J.map f = J') :=
  ⟨fun _ hJ => CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_central hp f hc hJ,
   fun _ hJ' => CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_central
     hp f hc hJ'⟩

theorem glaPLayer_map_eq_of_ker_le_center {p : ℕ} (hp : p.Prime) (f : G →* G')
    {X : Subgroup G} (hc : ∀ y ∈ X ⊓ f.ker, ∀ x ∈ X, x * y = y * x) :
    (GLAPLayer p X).map f = GLAPLayer p (X.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold GLAPLayer
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_central hp f hc hJ)
  · unfold GLAPLayer
    refine sSup_le fun J' hJ' => ?_
    obtain ⟨J, hJ, rfl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_central hp f hc hJ'
    exact Subgroup.map_mono (le_sSup hJ)

theorem glaPLayer_ne_bot_iff_map_ne_bot {p : ℕ} (hp : p.Prime) (f : G →* G')
    {X : Subgroup G} (hc : ∀ y ∈ X ⊓ f.ker, ∀ x ∈ X, x * y = y * x) :
    GLAPLayer p X ≠ ⊥ ↔ GLAPLayer p (X.map f) ≠ ⊥ := by
  have hmap := glaPLayer_map_eq_of_ker_le_center hp f hc (X := X)
  constructor
  · intro hX hbot
    have hle : GLAPLayer p X ≤ f.ker := by
      rw [← Subgroup.map_eq_bot_iff, hmap, hbot]
    rw [GLAPLayer] at hX
    rw [Ne, sSup_eq_bot] at hX
    push Not at hX
    obtain ⟨J, hJ, hJne⟩ := hX
    have hkerJ : J ≤ f.ker :=
      (show J ≤ GLAPLayer p X by rw [GLAPLayer]; exact le_sSup hJ).trans hle
    have hcomm : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hc x ⟨hJ.1 hx, hkerJ hx⟩ y (hJ.1 hy)
    rw [CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ] at hcomm
    exact hJne hcomm
  · intro hX' hbot
    apply hX'
    rw [← hmap, hbot, Subgroup.map_bot]

end CFSG

end
