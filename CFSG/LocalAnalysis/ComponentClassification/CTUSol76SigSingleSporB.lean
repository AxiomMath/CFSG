module

public import CFSG.Sporadic.Co1Block.Thirteen
public import CFSG.Sporadic.FischerOddCore.Fi24Block
public import CFSG.Sporadic.HNOddCore.CTILocal
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.Sporadic.Co2Schreier.Components
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.Sporadic.Ly
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporTools

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

open Sporadic.Co1Block in
theorem singleComponentCleanAt_Co1 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Co1) := by
  refine singleComponentCleanAt_of_primePow 13 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · rw [← card_quot_center_subgroupOf hK.1, pow_one]
    exact (cti_co1_involution_local_components_simple_quotient_divisible_by_thirteen
      hP hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)).2
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 13 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Co1
    rw [Sporadic.Co1.card_Co1]
    norm_num

theorem singleComponentCleanAt_Co2 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Co2) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  obtain ⟨e⟩ := hP
  exact Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e y hy2 _
    (isComponent_subgroupOf_of_isTwoComponentIn hK hq)

theorem singleComponentCleanAt_Fi22 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Fi22) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    rw [← card_quot_center_subgroupOf hK.1,
      Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e y hy2 _
        (isComponent_subgroupOf_of_isTwoComponentIn hK hq)]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Fi22
    rw [Sporadic.Fi22.card_Fi22]
    norm_num

open Sporadic.FischerOddCore in
theorem singleComponentCleanAt_Fi23 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Fi23) := by
  refine singleComponentCleanAt_of_primePow 11 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    rw [← card_quot_center_subgroupOf hK.1, pow_one]
    exact CTI_Fi23_involution_local_components_simple_quotient_divisible_by_eleven
      e y hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 11 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Fi23
    rw [Sporadic.Fi23.card_Fi23]
    norm_num

open Sporadic.FischerOddCore in
theorem singleComponentCleanAt_Fi24 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Fi24Prime) := by
  refine singleComponentCleanAt_of_primePow 11 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    rw [← card_quot_center_subgroupOf hK.1, pow_one]
    exact (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
      e y hy2 _ (isComponent_subgroupOf_of_isTwoComponentIn hK hq)).2
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 11 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Fi24prime
    rw [Sporadic.Fi24.card_Fi24prime]
    norm_num

theorem singleComponentCleanAt_HN :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .HN) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨e⟩ := hP
    rw [← card_quot_center_subgroupOf hK.1,
      Sporadic.HNOddCore.cti_hn_involution_local_components_simple_quotient_order e y hy2 _
        (isComponent_subgroupOf_of_isTwoComponentIn hK hq)]
    norm_num
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.HN
    rw [Sporadic.HN.card_HN]
    norm_num

theorem singleComponentCleanAt_J2 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .J2) := by
  refine singleComponentCleanAt_of_solvable fun T _ _ hT hP y K hy2 hK hq _ => ?_
  have h12 :=
    Sporadic.SmallOddCore.cti_j2_involution_local_components_ambient_centralizer_order_twelve hP hy2
      (isComponentOf_of_isTwoComponentIn hK hq)
  have := Fintype.ofFinite ↥(centralizer (K : Set T))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 2) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h12]; norm_num)

theorem singleComponentCleanAt_J4 :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .J4) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  exact RestrictedStd.Spor.j4NoComponentsInput T hP y hy2 _
    (isComponent_subgroupOf_of_isTwoComponentIn hK hq)

theorem singleComponentCleanAt_Th :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Th) := by
  refine singleComponentCleanAt_of_forall_false fun T _ _ hT hP y K hy2 hK hq _ => ?_
  have hch := ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two).2.2
    T hP).1 y hy2
  exact RestrictedStd.Spor.compsSatisfy_of_charP hch.1 (fun _ _ => False) _
    (isComponent_subgroupOf_of_isTwoComponentIn hK hq)

theorem singleComponentCleanAt_Ly :
    SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Ly) := by
  refine singleComponentCleanAt_of_primePow 7 1 fun T _ _ hT hP =>
    ⟨fun y K hy2 hK hq _ => ?_, ?_⟩
  · obtain ⟨hCq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple hP y hy2
    have htop := RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hCq
      (isComponent_subgroupOf_of_isTwoComponentIn hK hq)
    have hKC : K = centralizer ({y} : Set T) := by
      refine le_antisymm hK.1 fun g hg => ?_
      have : (⟨g, hg⟩ : centralizer ({y} : Set T)) ∈ K.subgroupOf (centralizer ({y} : Set T)) :=
        htop ▸ mem_top _
      exact this
    subst hKC
    rw [pow_one, Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv]
    change ¬ 7 ^ (2 * 1) ∣ Nat.card Blueprint.NativeSporadic.Ly
    rw [Sporadic.Ly.card_Ly]
    norm_num

end CFSG.ComponentClassification.Sol76.Sig
