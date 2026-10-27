module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Conj
public import CFSG.ClassicalInvolution.Q3.Q3AM289Shape
public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section LayerConj


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conj_mem_nbrCoreFam (hΩ : ConjInvariant Ω) (g : G) {M L : Subgroup G} {a : G}
    (hL : L ∈ nbrCoreFam Ω M a) : conjSub g L ∈ nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹) := by
  obtain ⟨N, hN, rfl⟩ := hL
  exact ⟨conjSub g N, omegaNbr_conj hΩ hN g, (exactCore3_conjSub g a N).symm⟩

theorem conj_inv_mem_nbrCoreFam (hΩ : ConjInvariant Ω) (g : G) {M L : Subgroup G} {a : G}
    (hL : L ∈ nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹)) : conjSub g⁻¹ L ∈ nbrCoreFam Ω M a := by
  have h := conj_mem_nbrCoreFam hΩ g⁻¹ hL
  rwa [conjSub_inv_conjSub, show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h

theorem conj_mem_centralizingMembers (hΩ : ConjInvariant Ω) (g : G) {M L : Subgroup G} {a : G}
    (hL : L ∈ centralizingMembers (nbrCoreFam Ω M a) {a}) :
    conjSub g L ∈ centralizingMembers (nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹))
      {g * a * g⁻¹} := by
  refine ⟨conj_mem_nbrCoreFam hΩ g hL.1, ?_⟩
  have h2 := conjSub_mono (n := g) hL.2
  rwa [CFSG.ClassicalInvolution.Balance.conjSub_centralizer_singleton] at h2

theorem conj_inv_mem_centralizingMembers (hΩ : ConjInvariant Ω) (g : G) {M L : Subgroup G}
    {a : G} (hL : L ∈ centralizingMembers (nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹))
      {g * a * g⁻¹}) : conjSub g⁻¹ L ∈ centralizingMembers (nbrCoreFam Ω M a) {a} := by
  refine ⟨conj_inv_mem_nbrCoreFam hΩ g hL.1, ?_⟩
  have h2 := conjSub_mono (n := g⁻¹) hL.2
  rwa [CFSG.ClassicalInvolution.Balance.conjSub_centralizer_singleton,
    show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h2

theorem nbrLayer_conj (hΩ : ConjInvariant Ω) (g : G) (M : Subgroup G) (a : G) :
    nbrLayer Ω (conjSub g M) (g * a * g⁻¹) = conjSub g (nbrLayer Ω M a) := by
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    have h1 := conj_inv_mem_centralizingMembers hΩ g (M := M) (a := a) hL
    have h2 : conjSub g⁻¹ L ≤ nbrLayer Ω M a := le_centralizingLayer h1
    have h3 := conjSub_mono (n := g) h2
    rwa [conjSub_conjSub_inv] at h3
  · show (nbrLayer Ω M a).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_centralizingLayer (conj_mem_centralizingMembers hΩ g hL)

theorem layerS3_conj (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G} (g : G)
    (h : LayerS3 Ω M a) : LayerS3 Ω (conjSub g M) (g * a * g⁻¹) := by
  unfold LayerS3 at h ⊢
  exact Q3AM289.exists_lieSystem_conj_of_eq g (nbrLayer_conj hΩ g M a)
    (fun L hL => conj_mem_centralizingMembers hΩ g hL)
    (fun L hL => conj_inv_mem_centralizingMembers hΩ g hL)
    (fun k => k = CompData.model .PSU 3 ∨ k = CompData.model .G2 0 ∨
      k = CompData.model .trialityD4 0) h

theorem layerS3_of_mem [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (h : BadStd8 Ω K J S R T W z t) (hK : LayerS3 Ω K z) {M : Subgroup G}
    (hM : M ∈ Ω) {a : G} (ha : IsUniqueInvolution M a) : LayerS3 Ω M a := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  obtain ⟨g, hg⟩ := h.std.stand.trans M hM
  have hz' : IsUniqueInvolution M (g * z * g⁻¹) := hg ▸ h.std.hz.conj g
  have hae : a = g * z * g⁻¹ := by
    rcases ha.unique (g * z * g⁻¹) hz'.mem hz'.sq with h1 | h1
    · exact absurd h1 hz'.ne_one
    · exact h1.symm
  subst hg
  rw [hae]
  exact layerS3_conj hΩ.conjInvariant g hK

theorem s3Shape_layerFam {M : Subgroup G} {a : G} (h : LayerS3 Ω M a) :
    Q3T8.Asc77.S3Shape (layerFam Ω M a) := by
  obtain ⟨ι, -, D, i₁, hi, hk⟩ := h
  exact Q3T8.Asc77.S3Shape.of_lieSystemData3 D hi hk

end LayerConj

end CFSG.ClassicalInvolution.Q3.Q3AM
