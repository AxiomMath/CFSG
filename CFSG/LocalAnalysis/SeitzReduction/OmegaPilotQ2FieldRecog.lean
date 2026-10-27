module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldNbr
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosMinus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)

@[expose] def OmegaMinusTwoFieldRecognitionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
          (modelToG e (anisoPerp (K := K) (by omega) b c)) .field →
        (∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
          Nonempty (centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
            matrixProjectiveDerived (coordinateQuadPlus (n - 1) F))) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Nonempty (anisoNeighbourJoin L (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
            matrixProjectiveDerived (coordinateQuadPlus n F))

section Minus


theorem omegaMinusTwoFieldGlobalInput_of_recognition (h : OmegaMinusTwoFieldRecognitionInput) :
    OmegaMinusTwoFieldGlobalInput :=
  fun G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow =>
    h G L hset n hn K b c hirr hK2 e t ht hKt hnn hN hrow fun F _ _ _ hF =>
      nonempty_centralizerPerfectCore_mulEquiv_anisoTorus_two hset hn hK2 hirr e ht hKt hN hrow F
        hF

theorem omegaMinusTwoRowInput_field_of_recognition (hgen : OmegaMinusTwoFieldGenInput)
    (hrec : OmegaMinusTwoFieldRecognitionInput) : OmegaMinusTwoRowInput .field :=
  omegaMinusTwoRowInput_field_of_inputs hgen (omegaMinusTwoFieldGlobalInput_of_recognition hrec)

end Minus

@[expose] def OmegaPlusTwoFieldRecognitionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoPerp (K := K) m b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1) →
        OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr))
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c))
          .field →
        (∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 →
          Nonempty (centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) F))) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
          Nonempty (anisoNeighbourJoin L (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) F))

section Plus


theorem omegaPlusTwoFieldGlobalInput_of_recognition (h : OmegaPlusTwoFieldRecognitionInput) :
    OmegaPlusTwoFieldGlobalInput :=
  fun G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow =>
    h G L hset m hm K b c hirr hK2 e t ht hKt hnn hN hrow fun F _ _ _ hF =>
      nonempty_centralizerPerfectCore_mulEquiv_plusAnisoTorus_two hset hm hK2 hirr e ht hKt hN hrow
        F hF

theorem omegaPlusTwoRowInput_field_of_recognition (hgen : OmegaPlusTwoFieldGenInput)
    (hrec : OmegaPlusTwoFieldRecognitionInput) : OmegaPlusTwoRowInput .field :=
  omegaPlusTwoRowInput_field_of_inputs hgen (omegaPlusTwoFieldGlobalInput_of_recognition hrec)

theorem omegaPlusTwoInput_of_recognition (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (hgen : OmegaPlusTwoFieldGenInput)
    (hrec : OmegaPlusTwoFieldRecognitionInput) (hswap : OmegaPlusTwoRowInput .swap) :
    OmegaPlusTwoInput :=
  omegaPlusTwoInput_of_inputs h10 hcat (omegaPlusTwoRowInput_field_of_recognition hgen hrec) hswap

end Plus

section MinusInput


theorem omegaMinusTwoInput_of_recognition (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (hgen : OmegaMinusTwoFieldGenInput)
    (hrec : OmegaMinusTwoFieldRecognitionInput) (hswap : OmegaMinusTwoRowInput .swap) :
    OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_rows h10 hcat (omegaMinusTwoRowInput_field_of_recognition hgen hrec) hswap

end MinusInput

end CFSG.SeitzReduction.OmegaPilot
