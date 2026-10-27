module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26A02
import CFSG.ClassicalInvolution.Asc77.AscT8YC7Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY

@[expose] def SingleFrameFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (Q3T7.layerFam3 Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          ∀ F : FrameData Ω W K J z t, ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K,
            ∃ j, M = (F.ρ j).K
end T8YY
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8YY
open CFSG.ClassicalInvolution.Asc77.T8YY

@[expose] def SingleFrameFact0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (Q3T7.layerFam3 Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          ∀ F : FrameData Ω W K J z t, ∀ M ∈ omegaNbr Ω K, ∃ j, M = (F.ρ j).K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
theorem neighbours_of_frame_of_zero (hs : Std8 Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) (h0 : ∀ M ∈ omegaNbr Ω K, ∃ j, M = (F.ρ j).K) :
    ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K, ∃ j, M = (F.ρ j).K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  exact CFSG.ClassicalInvolution.Asc77.T8YY.neighbours_of_frame_of_zero_of hΩ.conjInvariant hs.stand.mem
    hs.stand.trans F h0

theorem singleFrameFact_of_zero (h : SingleFrameFact0) : SingleFrameFact := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα F
  exact neighbours_of_frame_of_zero hs F (h G Ω K J S R T W z t hs hdisc hμ hne huni hα F)
end T8YY
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
