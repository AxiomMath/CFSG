module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporTools
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCo3
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Co3

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem card_quot_center_eq_of_isSimpleGroup {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ a b : K, a * b ≠ b * a) : Nat.card (K ⧸ center K) = Nat.card K :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hK)).trans
    QuotientGroup.quotientBot).toEquiv

theorem singleComponentCleanAt_HS :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .HS) := by
  refine singleComponentCleanAt_of_primePow 3 2 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨hKs, hKna, hKc⟩ :=
      Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360 hP hy2
        (isComponentOf_of_isTwoComponentIn hK hq)
    rw [card_quot_center_eq_of_isSimpleGroup hKna, hKc]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 3 ^ (2 * 2) ∣ Nat.card Blueprint.NativeSporadic.HS
    rw [Sporadic.HS.card_HS]
    norm_num

theorem singleComponentCleanAt_He :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .He) := by
  refine singleComponentCleanAt_of_primePow 2 6 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · rw [Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order hP hy2
      (isComponentOf_of_isTwoComponentIn hK hq)]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 2 ^ (2 * 6) ∣ Nat.card Blueprint.NativeSporadic.He
    rw [Sporadic.He.fam_he_order.1]
    norm_num

theorem singleComponentCleanAt_Suz :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Suz) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    rw [← card_quot_center_subgroupOf hK.1,
      Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e y hy2 _
        (isComponent_subgroupOf_of_isTwoComponentIn hK hq)]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Suz
    rw [Sporadic.Suz.card_Suz]
    norm_num

theorem singleComponentCleanAt_ON :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .ONan) := by
  refine singleComponentCleanAt_of_primePow 2 6 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · rw [← card_quot_center_subgroupOf hK.1,
      Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order hP y
        hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 2 ^ (2 * 6) ∣ Nat.card Blueprint.NativeSporadic.ON
    rw [Sporadic.ON.card_ON]
    norm_num

theorem singleComponentCleanAt_McL :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .McL) := by
  refine singleComponentCleanAt_of_primePow 2 6 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    obtain ⟨f⟩ := RestrictedStd.Spor.mcl_inner_comps e y hy2 _
      (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
    rw [← card_quot_center_subgroupOf hK.1, Nat.card_congr f.toEquiv,
      Sporadic.SmallOddCore.card_mclX]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 2 ^ (2 * 6) ∣ Nat.card Blueprint.NativeSporadic.McL
    rw [Sporadic.McL.card_McL]
    norm_num

theorem singleComponentCleanAt_Co3 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Co3) := by
  refine singleComponentCleanAt_of_primePow 2 6 fun T _ _ hT hP => ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    have h : Nat.card (↥(K.subgroupOf (centralizer ({y} : Set T))) ⧸
        center ↥(K.subgroupOf (centralizer ({y} : Set T)))) ∈ RestrictedStd.Spor.co3Orders :=
      RestrictedStd.Spor.co3_inner_comps e y hy2 _
        (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
    rw [card_quot_center_subgroupOf hK.1] at h
    simp only [RestrictedStd.Spor.co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 2 ^ (2 * 6) ∣ Nat.card Blueprint.NativeSporadic.Co3
    rw [Sporadic.Co3.card_Co3]
    norm_num

end CFSG.ComponentClassification.Sol76.Sig
