module

public import CFSG.ClassicalInvolution.Asc77.AscT8YC3
public import CFSG.ClassicalInvolution.Asc77.AscT8YC4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8YY

variable (p f : ℕ) [Fact p.Prime]

@[expose] def SingleFrameFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        (∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
          ¬ DConnected (T8.layerFamQ Ω (z * s))) →
        alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ →
          ∀ F : FrameData Ω W K J z t, ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K,
            ∃ j, M = (F.ρ j).K

variable {p f}

theorem pureBCase_of_singleFrame (hV : LayerFrattiniFact p f) (hSF : SingleFrameFact p f) :
    PureBCase p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne huni hα
  exfalso
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  exact false_of_singleFrame hV hs hdisc hμ hne huni hα F
    (hSF G Ω K J S R T W z t hs hdisc hμ hne huni hα F)

theorem c26_13_sc_of_frattini_singleFrame (hV : LayerFrattiniFact p f)
    (hSF : SingleFrameFact p f) : C26_13_sc p f :=
  c26_13_sc_of_facts hV (pureBCase_of_singleFrame hV hSF)

end T8YY

end CFSG.ClassicalInvolution.Asc77
