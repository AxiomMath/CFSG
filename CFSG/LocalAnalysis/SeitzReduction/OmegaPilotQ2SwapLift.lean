module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapEnd
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_anisoTorus (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {m f' : ℕ}
    (hN : ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
        (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) m f')
    (hr : OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
      (modelToG e (anisoPerp (K := K) (by omega) b c)) .swap) :
    ∃ P : SwapParam t (modelToG e (anisoPerp (K := K) (by omega) b c)),
      Function.Injective P.Ψ ∧
        P.Ψ.range = centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) := by
  have hKt := inf_centralizer_eq_zpowers_minus hset (by omega) hKc hirr e htC ht
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus hset.standardSetting.standard htC ht hKt
    (by omega) hirr e rfl rfl
  obtain ⟨-, htX, -, -, -, hDC, -, hZD⟩ := neighbour_data_anisoTorus (by omega) hirr e htC rfl rfl
  replace htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G) := htX
  obtain ⟨hLie, hOutD⟩ := lieModel_map_anisoPerp hKc hn hirr e rfl
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_anisoTorus_of_seitzSetting hset hKc (by omega) hirr e htC ht rfl htX rfl
  obtain ⟨htX', hrow⟩ := hr
  have hs : (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, sq, LinearPilot.mk_mul_mk_eq_one ht htX, map_one]
  have hS := swapCase_of_neighbourOvergroupOmega hs
    (commutator_eq_self_of_isQuasisimple_open hcomp.2.2) (ne_bot_of_isQuasisimple hcomp.2.2)
    (hN htX) hrow
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDC.trans inf_le_left)
    (UnitaryPilot.modelToG_le e _) hZD hOutD
    (SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hLie) hsyl hS

theorem exists_swapParam_plusAnisoTorus (hset : SeitzSetting G L) {m f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {m' f' : ℕ}
    (hN : ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr) :
            Set G))) ⟨t, htX⟩)
        (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr) :
              Set G))))) m' f')
    (hr : OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr))
      (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c)) .swap) :
    ∃ P : SwapParam t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoPerp (K := K) m b c)),
      Function.Injective P.Ψ ∧
        P.Ψ.range = centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
          (plusAnisoTorus m hirr)) := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_plusAnisoTorus hset.standardSetting.standard htC ht
    hKt hm hirr e' rfl rfl
  obtain ⟨-, htX, -, -, -, hDC, -, hZD⟩ := neighbour_data_plusAnisoTorus hm hirr e' htC rfl rfl
  replace htX : t ∈ centralizer (modelToG e' (plusAnisoTorus m hirr) : Set G) := htX
  obtain ⟨hLie, hOutD⟩ := lieModel_map_plusAnisoPerp hKc hm hirr e' rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard htC ht
    hKt hm hirr e' rfl htX rfl
  obtain ⟨htX', hrow⟩ := hr
  have hs : (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e' (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, sq, LinearPilot.mk_mul_mk_eq_one ht htX, map_one]
  have hS := swapCase_of_neighbourOvergroupOmega hs
    (commutator_eq_self_of_isQuasisimple_open hcomp.2.2) (ne_bot_of_isQuasisimple hcomp.2.2)
    (hN htX) hrow
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDC.trans inf_le_left)
    (UnitaryPilot.modelToG_le e' _) hZD hOutD
    (SeitzQ2.oddSchurTrivial_of_lieModel_POmegaMinus hLie) hsyl hS

end CFSG.SeitzReduction.OmegaPilot
