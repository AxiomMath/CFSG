module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf18CaseIB

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open in
theorem layerU3_not_normal
    {T : Type} [Group T] [Finite T] [CaseIAmbient T]
    {H : Subgroup T} (hf : U3LayerFacts H) (hHtop : H ≠ ⊤) (hΛ1 : layerU3 H ≠ ⊥) :
    ¬ (layerU3 H).Normal := by
  intro hN
  obtain ⟨N, _, hmodel, ⟨eN⟩, hcard⟩ := hf.model
  have hO : classicalInvolutionOddCore ↥(layerU3 H) = ⊥ := by
    have h : (classicalInvolutionOddCore ↥(layerU3 H)).map (layerU3 H).subtype =
        layerU3 H ⊓ classicalInvolutionOddCore T :=
      CFSG.ComponentClassification.OddCore.normal_intersection T (layerU3 H)
    rw [CaseIAmbient.oddCore_eq_bot (T := T), inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (layerU3 H).subtype_injective).mp h
  let eΛ : ↥(layerU3 H) ≃* N :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm.trans eN
  obtain ⟨hNs, -⟩ := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.u33_isSimpleGroup hmodel
  haveI : IsSimpleGroup ↥(layerU3 H) := eΛ.isSimpleGroup
  have hFle : genFittingFStar T ≤ layerU3 H := CaseIAmbient.fstar_le_of_normal hN hΛ1
  have hFeq : genFittingFStar T = layerU3 H := by
    have hFn : ((genFittingFStar T).subgroupOf (layerU3 H)).Normal :=
      (CFSG.ClassicalInvolution.genFittingFStar_normal T).subgroupOf _
    rcases hFn.eq_bot_or_eq_top with h | h
    · exfalso
      have hbot : genFittingFStar T = ⊥ :=
        (inf_eq_left.mpr hFle).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h))
      exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance hbot
    · exact le_antisymm hFle (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨eQ⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hmodel
  let eF : ↥(genFittingFStar T) ≃* _ := (MulEquiv.subgroupCongr hFeq).trans (eΛ.trans eQ)
  haveI := CFSG.GH74.KGroups.U33.finite_mulAut eF
  haveI : (genFittingFStar T).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal T
  have hT : Nat.card T ≤ 12096 := by
    rw [← CFSG.GH74.KGroups.U33.card_mulAut eF]
    refine Nat.card_le_card_of_injective (MulAut.conjNormal (H := genFittingFStar T)) ?_
    refine (injective_iff_map_eq_one _).mpr fun g hg => ?_
    have hgC : g ∈ Subgroup.centralizer (genFittingFStar T : Set T) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg
        (fun φ : MulAut ↥(genFittingFStar T) => ((φ ⟨x, hx⟩ : ↥(genFittingFStar T)) : T)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc x * g = g * x * g⁻¹ * g := by rw [h]
        _ = g * x := by group
    rw [CaseIAmbient.centralizer_fstar_eq_bot, Subgroup.mem_bot] at hgC
    exact hgC
  have hNcard : Nat.card N = 6048 := by
    rw [Nat.card_congr eQ.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  have hle : Nat.card T ≤ Nat.card H := by omega
  exact hHtop ((Subgroup.card_eq_iff_eq_top H).mp
    (le_antisymm (Subgroup.card_le_card_group H) hle))

theorem frameC201U3Section_proved : FrameC201U3Section :=
  frameC201U3Section_of_model
    (fun _ _ hN => CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.u33_involutions_conj hN)
    (fun _ _ hN => CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.u33_involution_eq_sq hN)
    (fun _ _ hN => CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.u33_isSimpleGroup hN)

theorem frameC201U3FalseF_proved : FrameC201U3FalseF := by
  intro T _ _ _ R t J zK zJ hh H hH hrow
  have hf := frameC201U3Section_proved T H hrow
  exact frame_false_of_u3LayerFacts CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
    hh hH hf fun hHtop hΛ1 => layerU3_not_normal hf hHtop hΛ1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
