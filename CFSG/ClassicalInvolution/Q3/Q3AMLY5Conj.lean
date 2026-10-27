module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AM289Lay
public import CFSG.ClassicalInvolution.Q3.Q3AMBadConj
public import CFSG.ClassicalInvolution.Q3.Q3AMLY3Thin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section LayerE4Conj


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerL3_conj (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G} (g : G)
    (h : LayerL3 Ω M a) : LayerL3 Ω (conjSub g M) (g * a * g⁻¹) := by
  unfold LayerL3 at h ⊢
  exact Q3AM289.exists_lieSystem_conj_of_eq g (nbrLayer_conj hΩ g M a)
    (fun L hL => conj_mem_centralizingMembers hΩ g hL)
    (fun L hL => conj_inv_mem_centralizingMembers hΩ g hL)
    (fun k => k = CompData.model .PSL 3) h

theorem layerM11_conj (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G} (g : G)
    (h : LayerM11 Ω M a) : LayerM11 Ω (conjSub g M) (g * a * g⁻¹) := by
  unfold LayerM11 at h ⊢
  exact Q3AM289.exists_lieSystem_conj_of_eq g (nbrLayer_conj hΩ g M a)
    (fun L hL => conj_mem_centralizingMembers hΩ g hL)
    (fun L hL => conj_inv_mem_centralizingMembers hΩ g hL)
    (fun k => k = CompData.m11) h

theorem layerE4_conj (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G} (g : G)
    (h : LayerE4 Ω M a) : LayerE4 Ω (conjSub g M) (g * a * g⁻¹) := by
  rcases h with h | h
  · exact Or.inl (layerL3_conj hΩ g h)
  · exact Or.inr (layerM11_conj hΩ g h)

theorem layerE4_of_mem [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (h : BadStd8 Ω K J S R T W z t) (hK : LayerE4 Ω K z) {M : Subgroup G}
    (hM : M ∈ Ω) {a : G} (ha : IsUniqueInvolution M a) : LayerE4 Ω M a := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  obtain ⟨g, hg⟩ := h.std.stand.trans M hM
  have hz' : IsUniqueInvolution M (g * z * g⁻¹) := hg ▸ h.std.hz.conj g
  have hae : a = g * z * g⁻¹ := by
    rcases ha.unique (g * z * g⁻¹) hz'.mem hz'.sq with h1 | h1
    · exact absurd h1 hz'.ne_one
    · exact h1.symm
  subst hg
  rw [hae]
  exact layerE4_conj hΩ.conjInvariant g hK

theorem exists_sysU_of_layerE4 {M : Subgroup G} {a : G} (h : LayerE4 Ω M a) :
    ∃ D : LieSystemDataU 3 1 (Fin 1)
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a),
      CompIs 3 1 (D.kind 0) .PSL 3 ∨ D.kind 0 = Q3.CompData.m11 := by
  rcases h with ⟨ι, -, D₃, i₁, hone, hk⟩ | ⟨ι, -, D₃, i₁, hone, hk⟩
  · obtain ⟨D, hD⟩ := exists_uniform_of_layer D₃ i₁ hone
    exact ⟨D, Or.inl (compIs_psl3 (hD.trans hk))⟩
  · obtain ⟨D, hD⟩ := exists_uniform_of_layer D₃ i₁ hone
    exact ⟨D, Or.inr (hD.trans hk)⟩

theorem layerE4_simple [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hN : NoTriangleAtEdge Ω K J) (hK : LayerE4 Ω K z) :
    IsSimpleGroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ∧
      ∃ x y : ↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z), x * y ≠ y * x := by
  refine ⟨?_, ?_⟩
  · obtain ⟨D, hD | hD⟩ := exists_sysU_of_layerE4 hK
    · exact layer_isSimple_of_T6 h hint hN D (Or.inl ⟨rfl, rfl⟩) hD
    · exact layer_isSimple_of_m11 D hD
  · obtain ⟨ζ, hζ⟩ := exists_isClassicalMember3_modOddIn h hint h.std.hJ
    have hnc := not_commutes_self_of_isClassicalMember3 hζ
    unfold Commutes at hnc
    push Not at hnc
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact ⟨x, y, hxy⟩

theorem layerE4_simple_of_mem [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G}
    {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) (hK : LayerE4 Ω K z)
    {M : Subgroup G} (hM : M ∈ Ω) {a : G} (ha : IsUniqueInvolution M a) :
    IsSimpleGroup (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) ∧
      ∃ x y : ↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a),
        x * y ≠ y * x := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  obtain ⟨g, hg⟩ := h.std.stand.trans M hM
  have hz' : IsUniqueInvolution M (g * z * g⁻¹) := hg ▸ h.std.hz.conj g
  have hae : a = g * z * g⁻¹ := by
    rcases ha.unique (g * z * g⁻¹) hz'.mem hz'.sq with h1 | h1
    · exact absurd h1 hz'.ne_one
    · exact h1.symm
  subst hg
  rw [hae]
  obtain ⟨hs, x, y, hxy⟩ := layerE4_simple h hint hN hK
  have hY := nbrLayer_conj hΩ.conjInvariant g K z
  let e := conjQuotEquiv g hY
  have := hs
  refine ⟨e.symm.isSimpleGroup, e x, e y, fun hc => hxy (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact hc

end LayerE4Conj

end CFSG.ClassicalInvolution.Q3.Q3AM
