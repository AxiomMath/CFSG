module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

section Edge

variable {Y : Type} [Group Y] [Finite Y]

theorem not_tightEdgeless_of_hasTwin {R : Subgroup Y}
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) (h : HasTwin R) :
    ¬ TightEdgeless R := by
  obtain ⟨K', ⟨hK'Ω, z, hzK, hzK'⟩, hne⟩ := h
  intro hedge
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := CoreAssembly.mem_conjClass_self _
  exact hedge _ hK₀ _ hK'Ω (Or.inl (Q3CL.T3.twin_mem_omegaNbr hΩ hK₀ hK'Ω hne hzK hzK'))

end Edge

section Exit

theorem exitOddFree_of_hasTwin (hSp : ModelFactSp62) (hD4 : ModelFactD42) {Y : Type} [Group Y]
    [Finite Y] (R : Subgroup Y) (c : Y)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore (secR R c))))
    (htw : HasTwin (tightCore (secR R c))) (x : SecQ R c)
    (Sb : Sylow 2 ↥(tightCore (secR R c)))
    (hex : TightEx (SecQ R c) (tightCore (secR R c)) Sb x ∨ TwinE4 (SecQ R c)) :
    TightInO2 x ∨ SecOddFree R c x := by
  have hΩ' : HypOmegaGen (CoreAssembly.conjClass (tightCore (tightCore (secR R c)))) := by
    rw [TwinEdge.tightCore_idem]; exact hΩ
  rcases hex with h1 | h1
  · rcases h1 with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact Or.inl h2
    · exact absurd he (not_tightEdgeless_of_hasTwin hΩ' htw)
    · exact absurd he (not_tightEdgeless_of_hasTwin hΩ' htw)
    · exact Or.inr (movedOddFreeIn_of_tightE4 hSp hD4 h4 x)
  · exact Or.inr (movedOddFreeIn_of_twinE4 hSp hD4 h1 x)

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf
