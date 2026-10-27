module

public import CFSG.ClassicalInvolution.Q3.Q3AMTri
public import CFSG.ClassicalInvolution.Q3.Q3AMTriT03A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Plain

variable {G : Type} [Group G]

theorem exists_nbr_of_mem_pspLayerFam {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G}
    {A : Subgroup (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))}
    (hA : A ∈ PspLayerFam Ω M a) : ∃ N ∈ omegaNbr Ω M, A = layerImage Ω M a N := by
  obtain ⟨_, ⟨L, ⟨⟨N, hN, rfl⟩, -⟩, hLY, rfl⟩, rfl⟩ := hA
  exact ⟨N, hN, rfl⟩

end Plain

section Triple


variable {G : Type} [Group G] [Finite G]

theorem pspTripleLeaf_proved : PspTripleLeaf := by
  intro _ G _ _ _ Ω K J S R T W z t K' _ hset hTri
  obtain ⟨F, hF, hinj, hcomm⟩ := hTri
  obtain ⟨N₀, h₀, e₀⟩ := exists_nbr_of_mem_pspLayerFam (hF 0)
  obtain ⟨N₁, h₁, e₁⟩ := exists_nbr_of_mem_pspLayerFam (hF 1)
  obtain ⟨N₂, h₂, e₂⟩ := exists_nbr_of_mem_pspLayerFam (hF 2)
  refine BadStd8.false_of_layerImage_commutes hset.bad h₀ h₁ h₂ ?_ ?_ ?_ ?_ ?_
  · intro a ha b hb
    exact hcomm 0 1 (by decide) a (by rw [e₀]; exact ha) b (by rw [e₁]; exact hb)
  · intro a ha b hb
    exact hcomm 0 2 (by decide) a (by rw [e₀]; exact ha) b (by rw [e₂]; exact hb)
  · intro h
    exact absurd (hinj (e₁.trans (h.trans e₀.symm))) (by decide)
  · intro h
    exact absurd (hinj (e₂.trans (h.trans e₀.symm))) (by decide)
  · intro h
    exact absurd (hinj (e₂.trans (h.trans e₁.symm))) (by decide)

end Triple

end CFSG.ClassicalInvolution.Q3.Q3AM
