module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Edge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Ident

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {Y : Type} [Group Y] {K M L L₂ L₃ : Subgroup Y} {V : Fin 3 → Subgroup Y}

theorem ae6Glue_of_aligned {ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k)} (hS : AE6Shape K M L L₂ L₃ V)
    (hT : AE6ModelTri) (al : AlignedFam K V ψ) : AE6Glue V := by
  obtain ⟨β, hβe, hβ01, hβ02, hβ12⟩ := hT (theta al (k := 0) (l := 1) (by decide))
    (theta al (k := 0) (l := 2) (by decide)) (theta al (k := 1) (l := 2) (by decide))
    (theta_aut hS al _) (theta_aut hS al _) (theta_aut hS al _) (theta_compat al)
  have pair : ∀ (k l : Fin 3) (hkl : k ≠ l), AE6EdgeCompat β k l (theta al hkl) →
      ∀ (g : ↥(V k)) (hg : (g : Y) ∈ V l),
        ((β l (ψ l ⟨g, hg⟩) : ↥(ae6ModelV l)) : AE6Om) = ((β k (ψ k g) : ↥(ae6ModelV k)) : AE6Om) := by
    intro k l hkl hc g hg
    have hmem : ((ψ k g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelE k l :=
      ⟨(ψ k g).2, (al.edge k l hkl.symm g).1 hg⟩
    exact hc ⟨_, hmem⟩ (ψ k g) (ψ l ⟨g, hg⟩) rfl (theta_val al hkl g hg ⟨_, hmem⟩ rfl).symm
  refine ⟨fun k => (ψ k).trans (β k), ?_, ?_⟩
  · intro k l g
    by_cases hkl : k = l
    · subst hkl
      exact ⟨fun _ => ((ψ k).trans (β k) g).2, fun _ => g.2⟩
    · exact (al.edge k l (Ne.symm hkl) g).trans (hβe k l (ψ k g))
  · intro k l g hg
    by_cases hkl : k = l
    · subst hkl
      rfl
    · fin_cases k <;> fin_cases l
      · exact absurd rfl hkl
      · exact (pair 0 1 (by decide) hβ01 g hg).symm
      · exact (pair 0 2 (by decide) hβ02 g hg).symm
      · exact pair 0 1 (by decide) hβ01 ⟨g, hg⟩ g.2
      · exact absurd rfl hkl
      · exact (pair 1 2 (by decide) hβ12 g hg).symm
      · exact pair 0 2 (by decide) hβ02 ⟨g, hg⟩ g.2
      · exact pair 1 2 (by decide) hβ12 ⟨g, hg⟩ g.2
      · exact absurd rfl hkl

theorem exists_alignedFam (hS : AE6Shape K M L L₂ L₃ V) (hT0 : AE6ModelEdgePairsMem)
    (ψ₀ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k))
    (hψ₀ : ∀ k, Carries (ψ₀ k) (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK)) :
    ∃ ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k), AlignedFam K V ψ := by
  choose ψ hc he using exists_aligned hS hT0 ψ₀ hψ₀
  exact ⟨ψ, ⟨hc, he⟩⟩

theorem ae6Glue_of_idents (hS : AE6Shape K M L L₂ L₃ V)
    (hid : ∀ k, ∃ A : AEIdent (ae6ConjIn (V k) K) 8, pSpan (ae6ConjIn (V k) K) = V k ∧ A.φ.ker = ⊥)
    (hR : AE6ModelAE8) (hT0 : AE6ModelEdgePairsMem) (hT : AE6ModelTri) : AE6Glue V := by
  have h₀ : ∀ k, ∃ ψ : ↥(V k) ≃* ↥(ae6ModelV k),
      Carries ψ (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK) := by
    intro k
    obtain ⟨A, hspan, hker⟩ := hid k
    obtain ⟨ρ, hρ₁, hρ₂⟩ := hR k
    exact exists_vertexIso A hspan hker ρ hρ₁ hρ₂
  choose ψ₀ hψ₀ using h₀
  obtain ⟨ψ, al⟩ := exists_alignedFam hS hT0 ψ₀ hψ₀
  exact ae6Glue_of_aligned hS hT al

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
