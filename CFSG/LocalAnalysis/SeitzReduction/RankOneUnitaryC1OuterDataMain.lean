module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataChain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def U3C1OuterLevelDataHighInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k → U3C1CartanFpf L T D d →
    2 ≤ k → ∃ U U₁ : Subgroup G, U3C1OuterLevelData G L f t T D V U U₁ k

section Certificates


theorem u3C1OuterLevelDataFpfInput_of_high (hH : U3C1OuterLevelDataHighInput) :
    U3C1OuterLevelDataFpfInput := by
  intro G _ _ L f t T R₂ D d V k H hC
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k = 1 := by have := H.conf.one_le; omega
    subst hk1
    exact U3Start.outerData_one H hC
  · exact hH G L f t T R₂ D d V k H hC hk

theorem u3C1NcycSylowStageInput_of_high (hH : U3C1OuterLevelDataHighInput)
    (hM1 : U3C1OuterMuOneInput) (hM1S : U3C1OuterMuOneSylowInput) : U3C1NcycSylowStageInput :=
  u3C1NcycSylowStageInput_of_dataFpf (u3C1OuterLevelDataFpfInput_of_high hH) hM1 hM1S

end Certificates

end CFSG.SeitzReduction.RankOne
