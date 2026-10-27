module

public import CFSG.CharacterTheory.Semidihedral.SmallerRecognitionOddCoreControl
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOddCoreControl
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ABGTheoremB.Setting
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion
open CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Semidihedral.SmallerRecognitionOddCoreControl
open CFSG.Wreathed.SmallerRecognitionOddCoreControl

variable {G : Type} [Group G]

namespace WorkingI

theorem centralizer_singleton_eq_inf_subgroupOf (H : Subgroup G) (t : H) :
    Subgroup.centralizer ({t} : Set H) =
      (H ⊓ Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf H := by
  ext c
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    SetLike.coe_mem, true_and, Subtype.ext_iff, Subgroup.coe_mul]

theorem map_oddCore_centralizer_eq_oddCoreIn (H : Subgroup G) (t : H) :
    ((CFSG.oddCore (Subgroup.centralizer ({t} : Set H))).map
      (Subgroup.centralizer ({t} : Set H)).subtype).map H.subtype =
        oddCoreIn (H ⊓ Subgroup.centralizer ({(t : G)} : Set G)) := by
  rw [centralizer_singleton_eq_inf_subgroupOf, oddCoreIn]
  simp only [CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore]
  exact CFSG.pPrimeCore_map_subgroupOf 2 _ H inf_le_left

theorem qd_odd_core_commutator_control
    [Finite G]
    (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G)
    (H : Subgroup G) (hH : H ≠ ⊤) (hQD : IsQDGroup H) (t : H) (ht : orderOf t = 2)
    (A : Subgroup H) (hA : IsPGroup 2 A) (hAC : A ≤ Subgroup.centralizer ({t} : Set H)) :
    ⁅A, (CFSG.oddCore (Subgroup.centralizer ({t} : Set H))).map
      (Subgroup.centralizer ({t} : Set H)).subtype⁆ ≤ CFSG.oddCore H := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨h, ⟨-, k, hk, hkP⟩ | ⟨hh, hhP⟩⟩ := hQD.sylow
  · obtain ⟨fP⟩ := hkP P
    have hcontrol := smaller_simple_recognition_produces_proper_subgroup_odd_core_control
      G hsd H hH hQD.noIndexTwo k hk P fP t ht A hAC hA
    simpa only [← CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore] using hcontrol
  · obtain ⟨eP⟩ := hhP P
    exact smaller_wreathed_recognition_gives_proper_subgroup_odd_core_commutator_control
      hrec H (lt_top_iff_ne_top.mpr hH) h hh P eP hQD.involutions_isConj hQD.noIndexTwo
      t ht A hA hAC

end WorkingI

open WorkingI in
theorem wreathedSetting_workingHypothesisI
    [Finite G] [IsSimpleGroup G]
    (hrec : SmallerWreathedRecognition G)
    (hsd : CFSG.Semidihedral.ProperSubgroupRegularity.SmallerSimpleRecognition G) :
    WorkingHypothesisI G := by
  intro H hH hQD y hyH hy T₁ hT₁H hT₁ hyT₁
  let t : H := ⟨y, hyH⟩
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact hy
  have hcomm : ∀ a ∈ T₁, a * y = y * a := by
    intro a ha
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := T₁)).is_comm.comm ⟨a, ha⟩ ⟨y, hyT₁⟩)
  have hA : IsPGroup 2 (T₁.subgroupOf H) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁H).toEquiv, IsKleinFour.card_four]
    norm_num
  have hAC : T₁.subgroupOf H ≤ Subgroup.centralizer ({t} : Set H) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hcomm a ha))
  have hcontrol := Subgroup.map_mono (f := H.subtype)
    (qd_odd_core_commutator_control hrec hsd H hH hQD t ht _ hA hAC)
  rwa [Subgroup.map_commutator, map_oddCore_centralizer_eq_oddCoreIn,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT₁H] at hcontrol

end CFSG.Wreathed.OriginalAllPrime
