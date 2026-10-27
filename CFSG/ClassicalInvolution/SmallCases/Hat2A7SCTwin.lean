module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCExact
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7T21D

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Twin


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K₀ : Subgroup G}

theorem oddCentralAt_of_twin_of_thmE (hE : A7ThmE) (hs : Std2A7 Ω K₀) {K' : Subgroup G}
    (hK' : K' ∈ twinSet Ω K₀) (hne : K' ≠ K₀) :
    ∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → OddCentralAt Ω L z := by
  intro L hL z hz
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨g, hg⟩ := hs.trans L hL
  obtain ⟨hK'Ω, w, hw, hw'⟩ := hK'
  have hw1 : IsUniqueInvolution L (g * w * g⁻¹) := by
    rw [← hg]
    exact hw.conj g
  have hK'L : conjSub g K' ∈ twinSet Ω L :=
    ⟨hΩ.conjInvariant g K' hK'Ω, g * w * g⁻¹, hw1, hw'.conj g⟩
  have hne' : conjSub g K' ≠ L := by
    intro h
    have h1 : conjSub g K' = conjSub g K₀ := h.trans hg.symm
    have h2 := congrArg (conjSub g⁻¹) h1
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
    exact hne h2
  rcases a7_kPerp_eq_or_dConnected_of_thmE hE (hs.of_mem hL) hz hK'L hne' with h | ⟨-, hα⟩
  · exact oddCentralAt_of_kPerp_eq_twinSet hz h
  · refine oddCentralAt_of_alphaOf_bot hz fun J hJ t ht htz => hα J ⟨hJ.1, fun M hM => ?_⟩ t ht
    have hP : J ∈ KPerp Ω M := by
      rw [← kPerp_eq_of_twin hΩ hs.classical hL hM]
      exact Or.inr hJ
    rcases hP with h | h
    · exfalso
      obtain ⟨-, u, hu, hu'⟩ := hM
      subst h
      exact htz ((ht.eq hu').trans (hz.eq hu).symm)
    · exact h

theorem false_of_twin_of_thmE (hE : A7ThmE) (hs : Std2A7 Ω K₀) {K' : Subgroup G}
    (hK' : K' ∈ twinSet Ω K₀) (hne : K' ≠ K₀) (hedge : ¬ DEdgeless Ω) (hconn : DConnected Ω) :
    False :=
  false_of_oddCentral hs.toPre2A7 hedge hconn (oddCentralAt_of_twin_of_thmE hE hs hK' hne)

end Twin

end CFSG.ClassicalInvolution.Hat2A7S
