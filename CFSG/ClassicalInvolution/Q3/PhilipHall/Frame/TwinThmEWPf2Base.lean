module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf2Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Pf2Base

@[expose] def E18_5Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → (⨆ J ∈ Ω, J) = ⊤

theorem exists_orderOf_eq_four_of_mem_RSet_gen {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) :
    ∃ u ∈ R, orderOf u = 4 := by
  exact TwinThmE.exists_orderOf_eq_four_of_mem_RSet_gen hΩ hR

end Pf2Base

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
