module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh Ah : Subgroup Γ}

theorem lit_phi_of_quotIso [(Zh.subgroupOf Gh).Normal]
    (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x) (hAG : Ah ≤ Gh)
    (hq : IsQuotIso (normIn Gh Ah) (Gh ⊓ centralizerSection Ah Zh) (Equiv.Perm (Fin 6))) :
    ∃ φ : ↥(normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)) →* Equiv.Perm (Fin 6),
      Function.Surjective φ ∧
      ∀ g : ↥(normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)),
        φ g = 1 ↔ ∀ a ∈ Ah.subgroupOf Gh, ⁅a, (g : ↥Gh)⁆ ∈ Zh.subgroupOf Gh := by
  let N : Subgroup ↥Gh := normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)
  have hN : N = (normIn Gh Ah).subgroupOf Gh := lit_normalizer_eq hAG
  let ι : ↥N →* ↥(normIn Gh Ah) :=
    MonoidHom.mk'
      (fun g => ⟨((g : ↥Gh) : Γ), by
        have h : (g : ↥Gh) ∈ (normIn Gh Ah).subgroupOf Gh := by
          rw [← hN]; exact g.2
        exact Subgroup.mem_subgroupOf.mp h⟩)
      (fun g h' => by ext; rfl)
  have hι_surj : Function.Surjective ι := by
    intro n
    have hnGh : (n : Γ) ∈ Gh := (Subgroup.mem_inf.mp n.2).1
    let g0 : ↥Gh := ⟨(n : Γ), hnGh⟩
    have hg0 : g0 ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact n.2
    exact ⟨⟨g0, hg0⟩, Subtype.ext rfl⟩
  obtain ⟨_hC_le, ψ, hψ_surj, hψ_ker⟩ := hq
  refine ⟨ψ.comp ι, hψ_surj.comp hι_surj, ?_⟩
  intro g
  constructor
  · intro h
    have hker : ι g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact h
    rw [hψ_ker] at hker
    have hmem : ((g : ↥Gh) : Γ) ∈ Gh ⊓ centralizerSection Ah Zh :=
      Subgroup.mem_subgroupOf.mp hker
    have hmem' : (g : ↥Gh) ∈ (Gh ⊓ centralizerSection Ah Zh).subgroupOf Gh := by
      rw [Subgroup.mem_subgroupOf]; exact hmem
    have hlitC : (g : ↥Gh) ∈ litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) := by
      rw [lit_litC_eq hZc hAG]; exact hmem'
    exact (mem_litC.mp hlitC).2
  · intro h
    have hnorm : (g : ↥Gh) ∈ normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh) := g.2
    have hlitC : (g : ↥Gh) ∈ litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) := by
      rw [mem_litC]; exact ⟨hnorm, h⟩
    have hmem' : (g : ↥Gh) ∈ (Gh ⊓ centralizerSection Ah Zh).subgroupOf Gh := by
      rw [← lit_litC_eq hZc hAG]; exact hlitC
    have hmem : ((g : ↥Gh) : Γ) ∈ Gh ⊓ centralizerSection Ah Zh :=
      Subgroup.mem_subgroupOf.mp hmem'
    have hker : ι g ∈ ψ.ker := by
      rw [hψ_ker, Subgroup.mem_subgroupOf]
      exact hmem
    rw [MonoidHom.mem_ker] at hker
    exact hker

end CFSG.OddStandard.HigherRank.YamadaG23
