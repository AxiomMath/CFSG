module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelLUMap

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

structure FusedPkg (Gs : Type) [Group Gs] (q : ℕ) (ε : ℤ) (z' : Gs) (S' : Sylow 2 Gs)
    (E₁ E₂ : Subgroup Gs) (t' u' n' : Gs) : Prop where
  data : LUModelData Gs q ε z' S' E₁ E₂ t' u'
  n_mem : n' ∈ (S' : Subgroup Gs)
  n_norm₁ : n' ∈ normalizer (E₁ : Set Gs)
  n_norm₂ : n' ∈ normalizer (E₂ : Set Gs)
  n_sq : n' * n' ∈ E₁ ⊔ E₂
  dec : ∀ s ∈ (S' : Subgroup Gs), ∃ k ∈ (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂),
    s = k ∨ s = k * t' ∨ s = k * n' ∨ s = k * (t' * n')
  layer : IVK.Ez z' = E₁ ⊔ E₂
  pgl : FusedPGL z' E₁ n' q
  pgl₂ : FusedPGL z' E₂ n' q

@[expose] def FusedModelLeaf : Prop :=
  ∀ (Gs : Type) [Group Gs] [Finite Gs] (p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (S' : Sylow 2 Gs) (z' : Gs),
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' →
      ((p ^ f % 8 = 5 ∧ LieModel Gs .PSL 4 p f) →
        ∃ (E₁ E₂ : Subgroup Gs) (t' u' n' : Gs), FusedPkg Gs (p ^ f) 1 z' S' E₁ E₂ t' u' n') ∧
      ((p ^ f % 8 = 3 ∧ LieModel Gs .PSU 4 p f) →
        ∃ (E₁ E₂ : Subgroup Gs) (t' u' n' : Gs), FusedPkg Gs (p ^ f) (-1) z' S' E₁ E₂ t' u' n')

theorem FusedPkg.map {G H : Type} [Group G] [Group H] [Finite G] [Finite H] (Φ : G ≃* H) {q : ℕ}
    {ε : ℤ} {z : G} {S : Sylow 2 G} {S' : Sylow 2 H}
    (hS : (S' : Subgroup H) = (S : Subgroup G).map Φ.toMonoidHom) {E₁ E₂ : Subgroup G} {t u n : G}
    (h : FusedPkg G q ε z S E₁ E₂ t u n) :
    FusedPkg H q ε (Φ z) S' (E₁.map Φ.toMonoidHom) (E₂.map Φ.toMonoidHom) (Φ t) (Φ u) (Φ n) := by
  have hmem : ∀ x : G, x ∈ (S : Subgroup G) → Φ x ∈ (S' : Subgroup H) := fun x hx => by
    rw [hS]; exact ⟨x, hx, rfl⟩
  refine ⟨CFSG.GH74.GLS.Stage2.Final.ModelLUT.luModelData_map Φ hS h.data, hmem n h.n_mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.GH74.GLS.Stage2.Final.ModelLUT.normalizer_map Φ h.n_norm₁
  · exact CFSG.GH74.GLS.Stage2.Final.ModelLUT.normalizer_map Φ h.n_norm₂
  · rw [← map_mul, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem _ h.n_sq
  · intro s' hs'
    rw [hS] at hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    obtain ⟨k, hk, hcases⟩ := h.dec s hs
    refine ⟨Φ k, ?_, ?_⟩
    · refine ⟨hmem k hk.1, ?_⟩
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem _ hk.2
    · rcases hcases with h1 | h1 | h1 | h1
      · left; rw [h1]; rfl
      · right; left; rw [h1, map_mul]; rfl
      · right; right; left; rw [h1, map_mul]; rfl
      · right; right; right; rw [h1, map_mul, map_mul]; rfl
  · have hEz : (IVK.Ez z).map Φ.toMonoidHom = IVK.Ez (Φ z) := by
      unfold IVK.Ez
      rw [Subgroup.map_map, ← CFSG.GH74.GLS.Stage2.Final.ModelLT.subtype_comp_centralizerEquiv Φ z,
        ← Subgroup.map_map, CFSG.GH74.GLS.Stage2.Final.ModelLT.layer_map_equiv
          (CFSG.GH74.GLS.Stage2.Final.ModelLT.centralizerEquiv Φ z)]
    rw [← hEz, h.layer, Subgroup.map_sup]
  · exact h.pgl.map Φ
  · exact h.pgl₂.map Φ

end CFSG.GH74.GLS.Stage1.Main
