module

public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_eq_sSup {p : ℕ} {X : Subgroup G} :
    GLAPLayer p X = sSup {L : Subgroup G | GLAPComponent p X L} := rfl

theorem gLBConj_glaPLayer_le {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    GLBConj g (GLAPLayer p X) ≤ GLAPLayer p X := by
  have hXg : GLBConj g X = X := gLBConj_eq_of_mem_normalizer hg
  have hS : ∀ J : Subgroup G, GLAPComponent p X J → GLAPComponent p X (GLBConj g J) := by
    intro J hJ
    have h := glaPComponent_gLBConj hJ g
    rwa [hXg] at h
  have key : GLAPLayer p X ≤ GLBConj g⁻¹ (GLAPLayer p X) := by
    rw [glaPLayer_eq_sSup]
    apply sSup_le
    intro J hJ
    have h1 : GLBConj g J ≤ GLAPLayer p X := le_sSup (hS J hJ)
    have h2 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g⁻¹ h1
    have h3 : GLBConj g⁻¹ (GLBConj g J) = J := by
      have h := gLBConj_gLBConj_inv g⁻¹ J
      rwa [inv_inv] at h
    rw [h3] at h2
    exact h2
  have h4 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g key
  rwa [gLBConj_gLBConj_inv] at h4

theorem normalizes_glaPLayer {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((GLAPLayer p X : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  apply le_antisymm
  · exact gLBConj_glaPLayer_le hg
  · have h := gLBConj_glaPLayer_le (p := p) (Subgroup.inv_mem _ hg)
    have h2 := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g h
    rwa [gLBConj_gLBConj_inv] at h2

end Layer

section Centralizer

variable {Q : Type} [Group Q]

theorem centralizer_zpowers_eq (x : Q) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({x} : Set Q) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro H h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact H x (Subgroup.mem_zpowers x)
  · intro H h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hc : Commute x g := H x rfl
    exact (hc.zpow_left n).eq

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.T156

end
