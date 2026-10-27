module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight2

theorem comm_of_mem_closure {G : Type*} [Group G] {s : Set G}
    (hs : ∀ u ∈ s, ∀ v ∈ s, u * v = v * u) {u v : G} (hu : u ∈ closure s)
    (hv : v ∈ closure s) : u * v = v * u := by
  have h1 : closure s ≤ centralizer s := (closure_le _).mpr fun x hx =>
    mem_centralizer_iff.mpr fun w hw => hs w hw x hx
  have h2 : u ∈ centralizer ((closure s : Subgroup G) : Set G) := by
    rw [centralizer_closure]
    exact h1 hu
  exact (mem_centralizer_iff.mp h2 v hv).symm

variable {X : Type} [Group X] [Finite X]

end Eight2

end CFSG.ComponentClassification.GSThmB
