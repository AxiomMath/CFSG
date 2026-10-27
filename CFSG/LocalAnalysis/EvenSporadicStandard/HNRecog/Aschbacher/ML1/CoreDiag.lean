module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreFibre

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

@[expose] def CoreHyp.graph (h : CoreHyp N N' θ θ' ψ φ z) : Subgroup (L × L') :=
  diag N φ h.iso.map_mul

theorem CoreHyp.mem_graph_iff (h : CoreHyp N N' θ θ' ψ φ z) (x : L) (x' : L') :
    (x, x') ∈ h.graph ↔ x ∈ N ∧ x' = φ x :=
  Iff.rfl

theorem CoreHyp.graph_le_fibre [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    h.graph ≤ fibre θ θ' ψ N φ := by
  intro p hp
  obtain ⟨x, x'⟩ := p
  obtain ⟨hx, rfl⟩ := (CoreHyp.mem_graph_iff h x x').mp hp
  rw [mem_fibre_iff]
  constructor
  · have hθ : θ x = 1 := (h.ker x).mpr hx
    have hθ' : θ' (φ x) = 1 := (h.ker' (φ x)).mpr (h.iso.mem x hx)
    rw [hθ', hθ, map_one]
  · intro y hy
    have h1 := h.iso.map_mul x hx y hy
    have h2 := h.iso.map_mul (x * y) (N.mul_mem hx hy) x⁻¹ (N.inv_mem hx)
    have h3 := h.phi_inv hx
    rw [h2, h1, h3]

theorem CoreHyp.graph_normal [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (h.graph.subgroupOf (fibre θ θ' ψ N φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff h.graph_le_fibre]
  rintro ⟨x, x'⟩ ⟨l, l'⟩ hg hl
  obtain ⟨hx, rfl⟩ := (CoreHyp.mem_graph_iff h x x').mp hg
  obtain ⟨_, hlc⟩ := (mem_fibre_iff θ θ' ψ N φ l l').mp hl
  show (l * x * l⁻¹, l' * φ x * l'⁻¹) ∈ h.graph
  rw [CoreHyp.mem_graph_iff]
  exact ⟨(inferInstance : N.Normal).conj_mem x hx l, (hlc x hx).symm⟩

theorem CoreHyp.z_not_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (⟨(z, 1), h.mem_fibre_z⟩ : fibre θ θ' ψ N φ) ∉ h.graph.subgroupOf (fibre θ θ' ψ N φ) := by
  intro hmem
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨_, h2⟩ := (CoreHyp.mem_graph_iff h z 1).mp hmem
  exact h.phiZ_ne_one h2.symm

theorem CoreHyp.zz'_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (⟨(z, φ z), h.mem_fibre_zz'⟩ : fibre θ θ' ψ N φ) ∈
      h.graph.subgroupOf (fibre θ θ' ψ N φ) := by
  rw [Subgroup.mem_subgroupOf]
  exact (CoreHyp.mem_graph_iff h z (φ z)).mpr ⟨h.z_mem, rfl⟩

theorem CoreHyp.isPGroup_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    IsPGroup 2 ↥(h.graph.subgroupOf (fibre θ θ' ψ N φ)) := by
  intro g
  have hmem : (g : L × L') ∈ h.graph := by
    have := g.2
    rwa [Subgroup.mem_subgroupOf] at this
  obtain ⟨hgN, hg2⟩ := (CoreHyp.mem_graph_iff h (g : L × L').1 (g : L × L').2).mp hmem
  obtain ⟨k, hk⟩ := h.pgroup _ hgN
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · simpa only [Subgroup.coe_pow, Subgroup.coe_one, Prod.pow_fst, Prod.fst_one] using hk
  · simp only [Subgroup.coe_pow, Subgroup.coe_one, Prod.pow_snd, Prod.snd_one]
    rw [hg2, ← h.phi_pow hgN, hk, h.phi_one]

end CFSG.EvenSporadicStandard.HNRecog.ML1
