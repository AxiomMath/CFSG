module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreDiag

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

theorem CoreHyp.inner_sq_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) {t : L × L'}
    (ht : t ∈ fibre θ θ' ψ N φ) (hθ : InnerInv (θ t.1)) : t ^ 2 ∈ h.graph := by
  classical
  let F : Subgroup (L × L') := fibre θ θ' ψ N φ
  have htF : t ∈ F := ht
  obtain ⟨q, hqN, hqsq⟩ := h.inner_exists t.1 hθ
  let δ : L × L' := (q, φ q)
  have hδgraph : δ ∈ h.graph := (CoreHyp.mem_graph_iff h q (φ q)).mpr ⟨hqN, rfl⟩
  have hδF : δ ∈ F := h.graph_le_fibre hδgraph
  let t₁ : L × L' := t * δ
  have ht₁F : t₁ ∈ F := F.mul_mem htF hδF
  have hfst : (t₁ ^ 2).1 = z := by
    rw [Prod.pow_fst]
    change (t.1 * q) ^ 2 = z
    exact hqsq
  have ht₁sqF : t₁ ^ 2 ∈ F := F.pow_mem ht₁F 2
  have key := (mem_fibre_iff θ θ' ψ N φ (t₁ ^ 2).1 (t₁ ^ 2).2).mp ht₁sqF
  have hθ'y : θ' (t₁ ^ 2).2 = 1 := by
    have h1 := key.1
    rw [hfst, (h.ker z).mpr h.z_mem, map_one] at h1
    exact h1
  have hyN' : (t₁ ^ 2).2 ∈ N' := (h.ker' (t₁ ^ 2).2).mp hθ'y
  have hcomm : ∀ n' ∈ N', (t₁ ^ 2).2 * n' = n' * (t₁ ^ 2).2 := by
    intro n' hn'
    obtain ⟨x, hxN, rfl⟩ := h.iso.surj n' hn'
    have hc := key.2 x hxN
    rw [hfst] at hc
    have hzx : z * x * z⁻¹ = x := by
      rw [← h.z_central x]
      group
    rw [hzx] at hc
    exact (eq_mul_inv_iff_mul_eq.mp hc).symm
  have hcentre := h.centre' (t₁ ^ 2).2 hyN' hcomm
  have hy_ne_one : (t₁ ^ 2).2 ≠ 1 := by
    have hθ't₁ : θ' t₁.2 = ψ (θ t.1) := by
      change θ' (t.2 * φ q) = ψ (θ t.1)
      rw [map_mul, ht.1, (h.ker' (φ q)).mpr (h.iso.mem q hqN), mul_one]
    have hinner : InnerInv (θ' t₁.2) := by
      rw [hθ't₁]
      exact InnerInv.map hθ ψ
    have hne := h.inner_sq_ne' t₁.2 hinner
    simpa [Prod.pow_snd] using hne
  have hy : (t₁ ^ 2).2 = φ z := hcentre.resolve_left hy_ne_one
  have ht₁sq_graph : t₁ ^ 2 ∈ h.graph :=
    (CoreHyp.mem_graph_iff h (t₁ ^ 2).1 (t₁ ^ 2).2).mpr
      ⟨by rw [hfst]; exact h.z_mem, by rw [hfst]; exact hy⟩
  have hgn : (h.graph.subgroupOf F).Normal := h.graph_normal
  have ht₁sq_sub : (⟨t₁, ht₁F⟩ : F) ^ 2 ∈ h.graph.subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    simpa using ht₁sq_graph
  have hδ_sub : (⟨δ, hδF⟩ : F) ∈ h.graph.subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact hδgraph
  have ht_eq : (⟨t, htF⟩ : F) = ⟨t₁, ht₁F⟩ * ⟨δ, hδF⟩⁻¹ := by
    apply Subtype.ext
    show t = t₁ * δ⁻¹
    rw [show t₁ = t * δ from rfl]
    group
  have hfinal_sub : (⟨t, htF⟩ : F) ^ 2 ∈ h.graph.subgroupOf F := by
    have hconj : (⟨t₁, ht₁F⟩ : F)⁻¹ * (⟨δ, hδF⟩ : F)⁻¹ * ⟨t₁, ht₁F⟩ ∈
        h.graph.subgroupOf F :=
      hgn.conj_mem' (⟨δ, hδF⟩ : F)⁻¹ ((h.graph.subgroupOf F).inv_mem hδ_sub)
        ⟨t₁, ht₁F⟩
    have heq : (⟨t, htF⟩ : F) ^ 2 =
        (⟨t₁, ht₁F⟩ : F) ^ 2 *
          ((⟨t₁, ht₁F⟩ : F)⁻¹ * (⟨δ, hδF⟩ : F)⁻¹ * ⟨t₁, ht₁F⟩) *
          (⟨δ, hδF⟩ : F)⁻¹ := by
      rw [ht_eq, pow_two]
      group
    rw [heq]
    exact (h.graph.subgroupOf F).mul_mem
      ((h.graph.subgroupOf F).mul_mem ht₁sq_sub hconj)
      ((h.graph.subgroupOf F).inv_mem hδ_sub)
  rw [Subgroup.mem_subgroupOf] at hfinal_sub
  simpa using hfinal_sub

end CFSG.EvenSporadicStandard.HNRecog.ML1
