module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.RankOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_involution_mem_distinguished_class {H Y : Subgroup G} {z w : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hY : Y < ⊤)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hwL : w ∈ properHull Y z) (hw : orderOf w = 2) :
    w ∈ involutionPointClass z := by
  let L := properHull Y z
  let zL : L := ⟨z, distinguished_mem_properHull Y z⟩
  let wL : L := ⟨w, hwL⟩
  have hzorder : orderOf zL = 2 :=
    (Subgroup.orderOf_coe zL).symm.trans h.local_datum.distinguished_order
  have hworder : orderOf wL = 2 := (Subgroup.orderOf_coe wL).symm.trans hw
  have hzInv : IsInvolution zL :=
    ⟨(orderOf_eq_prime_iff.mp hzorder).2, (orderOf_eq_prime_iff.mp hzorder).1⟩
  have hwInv : IsInvolution wL :=
    ⟨(orderOf_eq_prime_iff.mp hworder).2, (orderOf_eq_prime_iff.mp hworder).1⟩
  obtain ⟨l, hl⟩ :=
    (native_strong_embedding_of_order_conditions
      (properHull_strong_embedding h hY hzY hescape)).involutions_conjugate hzInv hwInv
  exact ⟨(l : G), congrArg Subtype.val hl⟩

theorem properHull_rank_two_commuting_class {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hY : Y < ⊤)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) :
    ∃ w : G, w ∈ properHull Y z ∧ orderOf w = 2 ∧
      w ∈ involutionPointClass z ∧ Commute z w ∧ w ≠ z := by
  let L := properHull Y z
  let zL : L := ⟨z, distinguished_mem_properHull Y z⟩
  obtain ⟨S, hzS, hzcenter⟩ := properHull_central_sylow h hzY hescape
  obtain ⟨E, hEcard, hEsq⟩ := twoRankAtLeastTwo_of_contains_sylow
    S (le_rfl : (S : Subgroup L) ≤ (S : Subgroup L))
    (native_rank_two_of_two_le_twoRank hrank)
  let V : Subgroup L := E.map (S : Subgroup L).subtype
  have hVcard : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective (S : Subgroup L).subtype_injective]
    exact hEcard
  have hVleS : V ≤ (S : Subgroup L) := Subgroup.map_subtype_le E
  have hzorder : orderOf zL = 2 :=
    (Subgroup.orderOf_coe zL).symm.trans h.local_datum.distinguished_order
  have hnotle : ¬ V ≤ Subgroup.zpowers zL := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hVcard, Nat.card_zpowers, hzorder] at hcard
    omega
  obtain ⟨w, hwV, hwZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  have hw1 : w ≠ 1 := fun heq => hwZ (heq ▸ (Subgroup.zpowers zL).one_mem)
  have hwz : w ≠ zL := fun heq => hwZ (heq ▸ Subgroup.mem_zpowers zL)
  have hwsq : w ^ 2 = 1 := by
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hwV
    exact congrArg (fun a : E => ((a : (S : Subgroup L)) : L)) (hEsq ⟨e, he⟩)
  have hworder : orderOf w = 2 := orderOf_eq_prime_iff.mpr ⟨hwsq, hw1⟩
  have hwGorder : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hworder
  have hcomm : Commute zL w := by
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter)
      (⟨w, hVleS hwV⟩ : (S : Subgroup L)))).symm
  refine ⟨(w : G), w.property, hwGorder,
    properHull_involution_mem_distinguished_class h hY hzY hescape w.property hwGorder,
    congrArg Subtype.val hcomm.eq, ?_⟩
  exact fun heq => hwz (Subtype.ext heq)

theorem properHull_rank_two_entire_oddCore_le_point {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hY : Y < ⊤)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : 2 ≤ twoRank (properHull Y z)) : properOddCore Y ≤ H := by
  obtain ⟨w, hwL, _, hwclass, hcomm, hne⟩ :=
    properHull_rank_two_commuting_class h hY hzY hescape hrank
  exact local_point_odd_subgroup_le_of_commuting_class h.local_datum hwclass hcomm hne
    (properOddCore Y) (properOddCore_card_odd Y)
    (sup_le (Subgroup.zpowers_le.mpr (subgroup_normalizes_properOddCore Y hzY))
      (Subgroup.zpowers_le.mpr
        (subgroup_normalizes_properOddCore Y (properHull_le Y hzY hwL))))

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
