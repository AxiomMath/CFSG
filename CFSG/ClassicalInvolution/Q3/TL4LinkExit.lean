module

public import CFSG.ClassicalInvolution.Q3.TL4LinkCases

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


@[expose] def TightLinkStarEdgeR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkTrans R t → ¬ DConnected (linkFam R t) →
        Disconnected.DEdgeless (linkFam R t) →
          ∃ L ∈ linkFam R t, (omegaStarNbr (linkFam R t) L).Nonempty

variable {r n : ℕ}

theorem tightLinkExitR_of (h : TightLinkStarEdgeR r n) : TightLinkExitR r n := by
  intro Y _ _ R S t hL hc hT hα htr hnc R' S' t' hd' hc' heq hO2 hx
  have hed : TightEdgeless R' := by
    rcases hx with hx | hx
    · exact hx.1
    · exact hx.1
  have hed' : Disconnected.DEdgeless (linkFam R t) := by
    have h1 : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R')) := hed
    rwa [heq] at h1
  refine ⟨htr, hnc, Or.inr (Or.inr (Or.inl ⟨hed', h Y R S t hL hc hT hα htr hnc hed', R', S',
    t', ⟨hd', hc', hed⟩, heq, hO2, ?_⟩))⟩
  rcases hx with hx | hx
  · exact Or.inl hx.2
  · exact Or.inr hx.2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
