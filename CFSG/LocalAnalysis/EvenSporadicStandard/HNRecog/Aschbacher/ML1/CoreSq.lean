module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreSqKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreSqInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CentralExt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf
open scoped commutatorElement

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

theorem CoreHyp.sq_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) {t : L × L'}
    (ht : t ∈ fibre θ θ' ψ N φ) (hθ : θ t.1 ^ 2 = 1) : t ^ 2 ∈ h.graph := by
  classical
  let F : Subgroup (L × L') := fibre θ θ' ψ N φ
  let π : ↥F →* A5 × A5 := θ.comp ((MonoidHom.fst L L').comp F.subtype)
  let Δ : Subgroup ↥F := h.graph.subgroupOf F
  haveI hΔN : Δ.Normal := h.graph_normal
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := h.surj g
    obtain ⟨l', hl'⟩ := h.fibre_proj₁ l
    exact ⟨⟨(l, l'), hl'⟩, hl⟩
  have hΔ : Δ ≤ π.ker := by
    intro d hd
    rw [MonoidHom.mem_ker]
    rw [Subgroup.mem_subgroupOf] at hd
    obtain ⟨hdN, -⟩ := (CoreHyp.mem_graph_iff h (d : L × L').1 (d : L × L').2).mp hd
    exact (h.ker _).mpr hdN
  have hker : ∀ k ∈ π.ker, (∀ f : ↥F, ⁅k, f⁆ ∈ Δ) ∧ k ^ 2 ∈ Δ := by
    intro k hk
    have hθk : θ (k : L × L').1 = 1 := hk
    constructor
    · intro f
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅k, f⁆ : ↥F) : L × L') = ⁅(k : L × L'), (f : L × L')⁆ := by
        change F.subtype ⁅k, f⁆ = ⁅F.subtype k, F.subtype f⁆
        rw [map_commutatorElement]
      rw [hcoe]
      exact CoreHyp.ker_comm_mem_graph h k.2 hθk f.2
    · rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_pow] using CoreHyp.ker_sq_mem_graph h k.2 hθk
  have hinner : ∀ (f : ↥F) (a : A5), a ^ 2 = 1 →
      (π f = (a, 1) ∨ π f = (1, a)) → f ^ 2 ∈ Δ := by
    intro f a ha2 hcases
    by_cases ha1 : a = 1
    · have hpf : π f = 1 := by
        rcases hcases with hh | hh <;> rw [ha1] at hh <;> exact hh
      exact (hker f hpf).2
    · rw [Subgroup.mem_subgroupOf]
      have hInner : InnerInv (θ (f : L × L').1) := by
        refine ⟨a, ha1, ha2, ?_⟩
        rcases hcases with hh | hh
        · exact Or.inl hh
        · exact Or.inr hh
      simpa only [Subgroup.coe_pow] using CoreHyp.inner_sq_mem_graph h f.2 hInner
  have hmain : (⟨t, ht⟩ : ↥F) ^ 2 ∈ Δ :=
    sq_mem_of_inner_sq_mem Δ π hπ hΔ hker hinner ⟨t, ht⟩ hθ
  rw [Subgroup.mem_subgroupOf] at hmain
  simpa only [Subgroup.coe_pow] using hmain

end CFSG.EvenSporadicStandard.HNRecog.ML1
