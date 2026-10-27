module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinHyps

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

@[expose] def ThinE64 (IH : Prop) : Prop :=
  IH → ∀ (G : Type) [Group G] [Finite G] (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G))
    (g : G), Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
      (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
      ¬ Nonempty (AEIdentOn (fam K (conjSub g (piGen π))) 7 AE.e64Sets AE.e64Sub)

@[expose] def ThinE29 (IH : Prop) : Prop :=
  IH → ∀ (G : Type) [Group G] [Finite G] (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G))
    (g : G), Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
      (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
      ¬ Nonempty (AEIdentOn (fam K (conjSub g (piGen π))) 8 AE.e29Sets AE.e29Sub)

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
