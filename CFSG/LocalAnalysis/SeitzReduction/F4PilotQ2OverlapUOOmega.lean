module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOParam7
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphSix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTParamMinus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOParam6

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.SeitzReduction.SymplecticPilot (q2OmIota q2OmMIota)

@[expose] def TwoOmegaPlusModelValues : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
    TwoGraphModelValues .omegaPlus8 K (StatedOmega (StatedQuadPlus (3 + 1) K))
      (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl)

@[expose] def TwoOmegaMinusModelValues : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0),
    TwoGraphModelValues .omegaMinus8 K (StatedOmega (StatedQuadMinus (3 + 1) K b c))
      (q2OmMIota (k := K) (r := 3) le_rfl hirr hK)

@[expose] def TwoOmegaPlusParamInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → TwoKindAt e t X₀ .omegaPlus8 →
          ∃ Φ : StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
              centralizerPerfectCore (subgroupToG e X₀),
            IsTwoGraphParam e X₀ (q2OmIota (k := K) (r := 3) (by norm_num) hK le_rfl) Φ

@[expose] def TwoOmegaMinusParamInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2),
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → TwoKindAt e t X₀ .omegaMinus8 →
          ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
            (Φ : StatedOmega (StatedQuadMinus (3 + 1) K b c) ≃*
              centralizerPerfectCore (subgroupToG e X₀)),
            IsTwoGraphParam e X₀ (q2OmMIota (k := K) (r := 3) le_rfl hirr hK) Φ

theorem twoGraphModelInput_omegaPlus8_of_inputs (hP : TwoOmegaPlusParamInput)
    (hV : TwoOmegaPlusModelValues) : TwoGraphModelInput .omegaPlus8 := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨Φ, hΦ⟩ := hP K hK X₀ hXJ hcyc hX₀ G L e t hw hk
  exact ⟨_, inferInstance, Finite.of_equiv _ Φ.symm.toEquiv, _, Φ, hΦ, hV K hK⟩

theorem twoGraphModelInput_omegaMinus8_of_inputs (hP : TwoOmegaMinusParamInput)
    (hV : TwoOmegaMinusModelValues) : TwoGraphModelInput .omegaMinus8 := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨b, c, hirr, Φ, hΦ⟩ := hP K hK X₀ hXJ hcyc hX₀ G L e t hw hk
  exact ⟨_, inferInstance, Finite.of_equiv _ Φ.symm.toEquiv, _, Φ, hΦ, hV K hK b c hirr⟩

theorem twoOverlapInvAt_omegaPlus8_of_inputs (hP : TwoOmegaPlusParamInput)
    (hV : TwoOmegaPlusModelValues) : TwoOverlapInvAt .omegaPlus8 :=
  twoOverlapInvAt_of_modelInput (twoGraphModelInput_omegaPlus8_of_inputs hP hV)

theorem twoOverlapInvAt_omegaMinus8_of_inputs (hP : TwoOmegaMinusParamInput)
    (hV : TwoOmegaMinusModelValues) : TwoOverlapInvAt .omegaMinus8 :=
  twoOverlapInvAt_of_modelInput (twoGraphModelInput_omegaMinus8_of_inputs hP hV)

@[expose] def TwoUnitary6BlockValuesInput : Prop :=
  ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
    Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      TwoUniBlockValues .unitary6 (Nat.zero_le 1) ι hι

@[expose] def TwoUnitary7BlockValuesInput : Prop :=
  ∀ (K F : Type) [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
    Nat.card K = 2 → Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
      (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
      TwoUniBlockValues .unitary7 le_rfl ι hι

theorem twoOverlapInvUnitaryOmegaInput_of_inputs (hU6 : TwoUnitary6BlockValuesInput)
    (hU7 : TwoUnitary7BlockValuesInput) (hPp : TwoOmegaPlusParamInput)
    (hVp : TwoOmegaPlusModelValues) (hPm : TwoOmegaMinusParamInput)
    (hVm : TwoOmegaMinusModelValues) : TwoOverlapInvUnitaryOmegaInput :=
  ⟨twoOverlapInvAt_unitary6_of_values hU6, twoOverlapInvAt_unitary7_of_values hU7,
    twoOverlapInvAt_omegaPlus8_of_inputs hPp hVp, twoOverlapInvAt_omegaMinus8_of_inputs hPm hVm⟩

end CFSG.SeitzReduction.F4Pilot
