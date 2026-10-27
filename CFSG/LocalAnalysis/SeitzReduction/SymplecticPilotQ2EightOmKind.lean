module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightGraphRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def SpTwoOmegaCTDataEightInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k κ) → NsOmegaCTData e κ

theorem spTwoOmegaKindEightInput_of_ctData {κ : Sp2mKind} (h : SpTwoOmegaCTDataEightInput κ) :
    SpTwoOmegaKindEightInput κ := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  exact sp2mKindType_nsGlobal_of_nsOmegaCTData hK le_rfl e (h G L hset K hK e t ht hKt hroot)

@[expose] def SpTwoOmegaPlusParamCTEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by norm_num) le_rfl e t k (Φ k)) →
        NsOmegaCTData e .omegaPlus

@[expose] def SpTwoOmegaMinusParamCTEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) →
        NsOmegaCTData e .omegaMinus

section Param


theorem spTwoOmegaCTDataEightInput_omegaPlus_of_paramCT (h : SpTwoOmegaPlusParamCTEightInput) :
    SpTwoOmegaCTDataEightInput .omegaPlus := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  choose Φ hΦ using fun k => exists_isNsOmPlusParam hset hK (by norm_num) le_rfl e htC ht k
    (hroot k)
  exact h G L hset K hK e t ht hKt hroot Φ hΦ

theorem spTwoOmegaCTDataEightInput_omegaMinus_of_paramCT (h : SpTwoOmegaMinusParamCTEightInput) :
    SpTwoOmegaCTDataEightInput .omegaMinus := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  choose Φ hΦ using fun k => exists_isNsOmMinusParam hset hK le_rfl e htC ht k (hroot k)
  exact h G L hset K hK e t ht hKt hroot Φ hΦ

end Param

@[expose] def SpTwoOmegaMinusAlignEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) →
        ∃ ε : Fin (3 + 1) → Bool, NsOmMinusAligned e fun k =>
          if ε k then (kOmMBetaC K 3 1 1).trans (Φ k) else Φ k

@[expose] def SpTwoOmegaMinusPlaceEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaMinus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) → NsOmMinusAligned e Φ →
          NsOmegaCTData e .omegaMinus

@[expose] def SpTwoOmegaPlusAlignEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by norm_num) le_rfl e t k (Φ k)) →
        ∃ ε : Fin (3 + 1) → Bool, NsOmPlusAligned e fun k =>
          if ε k then (kOmegaBetaC K 3).trans (Φ k) else Φ k

@[expose] def SpTwoOmegaPlusPlaceEightInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), NsKindSp e t k .omegaPlus) →
      ∀ Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
          centralizerPerfectCore (modelToG e (nsTorusSp K k)),
        (∀ k, IsNsOmPlusParam hK (by norm_num) le_rfl e t k (Φ k)) → NsOmPlusAligned e Φ →
          NsOmegaCTData e .omegaPlus

theorem spTwoOmegaMinusParamCTEightInput_of_align_place (hA : SpTwoOmegaMinusAlignEightInput)
    (hP : SpTwoOmegaMinusPlaceEightInput) : SpTwoOmegaMinusParamCTEightInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot Φ hΦ
  obtain ⟨ε, hε⟩ := hA G L hset K hK e t ht hKt hroot Φ hΦ
  refine hP G L hset K hK e t ht hKt hroot _ (fun k => ?_) hε
  split_ifs
  · exact (hΦ k).comp_betaC
  · exact hΦ k

theorem spTwoOmegaPlusParamCTEightInput_of_align_place (hA : SpTwoOmegaPlusAlignEightInput)
    (hP : SpTwoOmegaPlusPlaceEightInput) : SpTwoOmegaPlusParamCTEightInput := by
  intro G _ _ L hset K _ _ _ hK e t ht hKt hroot Φ hΦ
  obtain ⟨ε, hε⟩ := hA G L hset K hK e t ht hKt hroot Φ hΦ
  refine hP G L hset K hK e t ht hKt hroot _ (fun k => ?_) hε
  split_ifs
  · exact (hΦ k).comp_betaC
  · exact hΦ k

section Kind


theorem spTwoOmegaKindEightInput_omegaMinus_of_align_place (hA : SpTwoOmegaMinusAlignEightInput)
    (hP : SpTwoOmegaMinusPlaceEightInput) : SpTwoOmegaKindEightInput .omegaMinus :=
  spTwoOmegaKindEightInput_of_ctData (spTwoOmegaCTDataEightInput_omegaMinus_of_paramCT
    (spTwoOmegaMinusParamCTEightInput_of_align_place hA hP))

theorem spTwoOmegaKindEightInput_omegaPlus_of_align_place (hA : SpTwoOmegaPlusAlignEightInput)
    (hP : SpTwoOmegaPlusPlaceEightInput) : SpTwoOmegaKindEightInput .omegaPlus :=
  spTwoOmegaKindEightInput_of_ctData (spTwoOmegaCTDataEightInput_omegaPlus_of_paramCT
    (spTwoOmegaPlusParamCTEightInput_of_align_place hA hP))

end Kind

end CFSG.SeitzReduction.SymplecticPilot
