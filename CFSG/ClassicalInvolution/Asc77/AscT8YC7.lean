module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC6
import CFSG.ClassicalInvolution.Asc77.AscT8YC7Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8YY

variable (p f : ℕ) [Fact p.Prime]

@[expose] def SingleFrameFact0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (T8.layerFamQ Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          ∀ F : FrameData Ω W K J z t, ∀ M ∈ omegaNbr Ω K, ∃ j, M = (F.ρ j).K

variable {p f}

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem neighbours_of_frame_of_zero (hs : Std8 p f Ω K J S R T W z t)
    (F : FrameData Ω W K J z t) (h0 : ∀ M ∈ omegaNbr Ω K, ∃ j, M = (F.ρ j).K) :
    ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K, ∃ j, M = (F.ρ j).K := by
  exact neighbours_of_frame_of_zero_of hs.stand.hyp.conjInvariant hs.stand.mem hs.stand.trans F
    h0

theorem singleFrameFact_of_zero (h : SingleFrameFact0 p f) : SingleFrameFact p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα F
  exact neighbours_of_frame_of_zero hs F (h G Ω K J S R T W z t hs hdisc hμ hne huni hα F)

theorem c26_13_sc_of_center_singleFrame0 (hC : LayerCenterFact p f) (hSF : SingleFrameFact0 p f) :
    C26_13_sc p f :=
  c26_13_sc_of_center_singleFrame hC (singleFrameFact_of_zero hSF)

end T8YY

end CFSG.ClassicalInvolution.Asc77
