module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.EvenSmallLie.OmegaEight

section Omega8

theorem card_outer_omega8plus2 {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1) : Nat.card (Outer Y) = 6 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hY
  rw [Nat.card_congr (equivalence e).toEquiv, card_outer_omegaT]

end Omega8

end CFSG.ClassicalInvolution.Nobq
