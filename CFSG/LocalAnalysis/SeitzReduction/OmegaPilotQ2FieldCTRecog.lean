module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTGenMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldRecog

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.LieType CFSG.LieType.Universal
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open scoped MatrixGroups

section Data

variable {G : Type} [Group G]

theorem anisoNeighbourJoin_le [Finite G] {L X G₀ : Subgroup G}
    (hE : centralizerPerfectCore X ≤ G₀) (hL : L ≤ G₀) : anisoNeighbourJoin L X ≤ G₀ := by
  refine iSup_le fun l => ?_
  rw [← F4Pilot.map_centralizerPerfectCore (MulAut.conj (l : G))]
  rintro _ ⟨x, hx, rfl⟩
  change (l : G) * x * (l : G)⁻¹ ∈ G₀
  exact G₀.mul_mem (G₀.mul_mem (hL l.2) (hE hx)) (G₀.inv_mem (hL l.2))

@[expose] def AnisoCTData (L X : Subgroup G) (n : ℕ) (F : Type) [Field F] : Prop :=
  ∃ U : Fin n → Subgroup G,
    (∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i → U i ≤ centralizer (U j : Set G)) ∧
    (∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (B12 F).map θ = U i ∧ (B23 F).map θ = U j) ∧
    (∀ k, U k ≤ anisoNeighbourJoin L X) ∧ centralizerPerfectCore X ≤ ⨆ k, U k ∧ L ≤ ⨆ k, U k

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nonempty_iSup_mulEquiv_of_weakCT {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hF4 : 4 ≤ Nat.card F) (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      U i ≤ centralizer (U j : Set G))
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (B12 F).map θ = U i ∧ (B23 F).map θ = U j) :
    Nonempty ((⨆ k, U k : Subgroup G) ≃* matrixProjectiveDerived (coordinateQuadPlus n F)) := by
  obtain ⟨Ψ, -, hcen, hmodel⟩ :=
    exists_weakCT_spinPlus_of_pieces_two_pow hn hf hF hF4 U rfl hcomm hpair
  have hZ : center (⨆ k, U k : Subgroup G) = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  have hL : CFSG.Blueprint.LieModel (⨆ k, U k : Subgroup G) .POmegaPlus n 2 f :=
    CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  obtain ⟨e⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hL F hF
  exact ⟨e.trans (statedOmegaPlusEquiv F n (by omega))⟩

theorem nonempty_anisoNeighbourJoin_mulEquiv_of_ctData [Finite G] {L X : Subgroup G} {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hF4 : 4 ≤ Nat.card F)
    (h : AnisoCTData L X n F) :
    Nonempty (anisoNeighbourJoin L X ≃* matrixProjectiveDerived (coordinateQuadPlus n F)) := by
  obtain ⟨U, hcomm, hpair, hU, hE, hL⟩ := h
  have heq : anisoNeighbourJoin L X = ⨆ k, U k :=
    le_antisymm (anisoNeighbourJoin_le hE hL) (iSup_le hU)
  obtain ⟨e⟩ := nonempty_iSup_mulEquiv_of_weakCT hn hf hF hF4 U hcomm hpair
  exact ⟨(MulEquiv.subgroupCongr heq).trans e⟩

end Data

@[expose] def OmegaMinusTwoFieldCTDataInput : Prop :=
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
          AnisoCTData L (modelToG e (anisoTorus (K := K) (by omega) b c)) n F

@[expose] def OmegaPlusTwoFieldCTDataInput : Prop :=
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
          AnisoCTData L (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) (m + 2) F

theorem omegaMinusTwoFieldRecognitionInput_of_ctData (h : OmegaMinusTwoFieldCTDataInput) :
    OmegaMinusTwoFieldRecognitionInput := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨F, _, _, _, hF4, hD⟩ := h G L hset n hn K b c hirr hK2 e t ht hKt hnn hN hrow hpar
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4,
    nonempty_anisoNeighbourJoin_mulEquiv_of_ctData (f := 2) (by omega) (by norm_num)
      (by rw [hF4]; norm_num) (by omega) hD⟩

theorem omegaPlusTwoFieldRecognitionInput_of_ctData (h : OmegaPlusTwoFieldCTDataInput) :
    OmegaPlusTwoFieldRecognitionInput := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨F, _, _, _, hF4, hD⟩ := h G L hset m hm K b c hirr hK2 e t ht hKt hnn hN hrow hpar
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF4,
    nonempty_anisoNeighbourJoin_mulEquiv_of_ctData (f := 2) (by omega) (by norm_num)
      (by rw [hF4]; norm_num) (by omega) hD⟩

section Rows

theorem omegaMinusTwoInput_of_recognitionInput (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m)
    (hrec : OmegaMinusTwoFieldRecognitionInput) : OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_recognition h10 hcat omegaMinusTwoFieldGenInput_holds hrec
    omegaMinusTwoRowInput_swap

theorem omegaPlusTwoInput_of_recognitionInput (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m)
    (hrec : OmegaPlusTwoFieldRecognitionInput) : OmegaPlusTwoInput :=
  omegaPlusTwoInput_of_recognition h10 hcat omegaPlusTwoFieldGenInput_holds hrec
    omegaPlusTwoRowInput_swap

end Rows

end CFSG.SeitzReduction.OmegaPilot
