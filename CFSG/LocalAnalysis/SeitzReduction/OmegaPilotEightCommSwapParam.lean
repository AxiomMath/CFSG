module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEight
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_minusPairTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {m f' : ℕ}
    (hS : ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f' ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨hLt, hD, hDq, hXo⟩ :=
    bLift_inputs_minusPairTorus_of_four_le hset hKc hq le_rfl hirr k e htC ht hX hDe
  obtain ⟨-, -, -, -, -, -, hDXt, -, hZD, hOutD⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset hKc hq
    le_rfl hirr k e htC ht hX htX hDe
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hSchur : OddSchurTrivial D := by
    obtain ⟨hR, -⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr
    obtain ⟨E, _, _, hE, ⟨θ⟩⟩ := nonempty_orthDerived_mulEquiv_statedSU_of_six hKc hR
      (by rw [Module.finrank_fin_fun]) (exists_ne_zero_coordinateQuadMinus_three hirr)
    have hSU := SeitzQ2.oddSchurTrivial_statedSU hE (by norm_num : 2 ≤ 4)
      (fun h => absurd (congrArg Prod.fst h) (by norm_num))
    subst hDe
    exact hSU.of_mulEquiv ((LinearPilot.mapSymmMulEquiv e _).trans
      ((minusPairPerpEquivOfLe le_rfl hirr k).trans θ)).symm
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDXt.trans inf_le_left) hDL hZD
    hOutD hSchur hsyl hS

end CFSG.SeitzReduction.OmegaPilot
