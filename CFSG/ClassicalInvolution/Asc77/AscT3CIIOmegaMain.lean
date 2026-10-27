module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmegaStep

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected

section Induction

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem aStar_subset_dComp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hall : ∀ M ∈ Ω, ∃ L ∈ omegaNbr Ω M, L ∉ twinSet Ω M) :
    ∀ J ∈ aStar Ω K, J ∈ dComp Ω K := by
  have key : ∀ J, Relation.ReflTransGen (aGraphAdj Ω) K J → J ∈ Ω ∧ J ∈ dComp Ω K := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hbΩ, hbd⟩ := ih
      obtain ⟨hcΩ, hc⟩ := hbc
      refine ⟨hcΩ, ?_⟩
      rcases hc with hc | hc | ⟨hc, hcb⟩
      · exact Relation.ReflTransGen.trans hbd (aSet_mem_dComp hp hq hΩ hbΩ (hall b hbΩ) hc)
      · have h1 : b ∈ dComp Ω c := aSet_mem_dComp hp hq hΩ hcΩ (hall c hcΩ) hc
        exact Relation.ReflTransGen.trans hbd (reflTransGen_dAdj_symm hcΩ h1)
      · obtain ⟨-, z, hzb, hzc⟩ := hc
        exact Relation.ReflTransGen.tail hbd
          ⟨hcΩ, Or.inl (twin_mem_omegaNbr hΩ hbΩ hcΩ hcb hzb hzc)⟩
  exact fun J hJ => (key J hJ).2

end Induction

variable {p f : ℕ} [Fact p.Prime]

theorem omegaNbrTwin : OmegaNbrTwin p f := by
  intro G _ _ _ K J z t a g h L hL
  by_contra hLtw
  have hp := h.branch.odd
  have hq := h.branch.five
  have hΩ : HypOmegaMod p f (CoreAssembly.conjClass K) := h.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ M ∈ CoreAssembly.conjClass K, ∃ L' ∈ omegaNbr (CoreAssembly.conjClass K) M,
      L' ∉ twinSet (CoreAssembly.conjClass K) M := by
    rintro M ⟨g', rfl⟩
    refine ⟨conjSub g' L, omegaNbr_conj hΩ.conjInvariant hL g', fun hmem => hLtw ?_⟩
    have := twinSet_conj hΩ.conjInvariant hmem g'⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hdc := aStar_subset_dComp hp hq hΩ hKΩ hall
  refine h.branch.dDisconnected ?_
  intro K₁ h₁ J₁ hJ₁
  have hK₁ : K₁ ∈ dComp (CoreAssembly.conjClass K) K := hdc K₁ (by rw [h.star]; exact h₁)
  have hJ₁' : J₁ ∈ dComp (CoreAssembly.conjClass K) K := hdc J₁ (by rw [h.star]; exact hJ₁)
  exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hKΩ hK₁) hJ₁'

theorem sec20Setup_proved : Sec20Setup p f := sec20Setup_of omegaNbrTwin

end CFSG.ClassicalInvolution.Asc77.T3CII
