module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem centralizer_index_eq_pointClass_card [Finite G] (z : G) :
    (Subgroup.centralizer ({z} : Set G)).index = Nat.card (involutionPointClass z) := by
  apply Nat.mul_right_cancel (Nat.card_pos (α := Subgroup.centralizer ({z} : Set G)))
  exact (Subgroup.centralizer ({z} : Set G)).index_mul_card.trans
    (pointClass_card_mul_centralizer z).symm

theorem centralizer_sylow_of_odd_point_class [Finite G] (z : G) (hz : orderOf z = 2)
    (hodd : Odd (Nat.card (involutionPointClass z)))
    (P : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G)),
      (S : Subgroup G) =
        (P : Subgroup (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ∧
      (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) := by
  let C := Subgroup.centralizer ({z} : Set G)
  let U := (P : Subgroup C).map C.subtype
  have hCodd : Odd C.index := by
    rw [centralizer_index_eq_pointClass_card z]
    exact hodd
  have hPodd : Odd (P : Subgroup C).index := Nat.not_even_iff_odd.mp
    (fun heven => P.not_dvd_index (even_iff_two_dvd.mp heven))
  have hUodd : Odd U.index := by
    rw [Subgroup.index_map_subtype]
    exact hPodd.mul hCodd
  have hUtwo : IsPGroup 2 U := P.isPGroup'.map C.subtype
  let S : Sylow 2 G := hUtwo.toSylow hUodd.not_two_dvd_nat
  have hS : (S : Subgroup G) = U := IsPGroup.toSylow_coe _ _
  have hzU : z ∈ U := NormalGraph.centralizer_sylow_contains z hz P
  have hzS : z ∈ (S : Subgroup G) := by
    rw [hS]
    exact hzU
  have hUle : U ≤ C := by
    rintro x ⟨c, _, rfl⟩
    exact c.property
  refine ⟨S, hzS, hS, Subgroup.mem_center_iff.mpr ?_⟩
  intro c
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hUle (hS ▸ c.property))

theorem subgroup_centralizer_index_odd [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (hescapeA : ¬ A ≤ H) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    Odd (Subgroup.centralizer ({(⟨z, hzA⟩ : A)} : Set A)).index := by
  rw [centralizer_index_eq_pointClass_card]
  exact subgroup_full_class_card_odd h hzA hescapeA S hzS hzcenter

theorem subgroup_centralizer_sylow_is_ambient [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (hescapeA : ¬ A ≤ H) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (P : Sylow 2 (Subgroup.centralizer ({(⟨z, hzA⟩ : A)} : Set A))) :
    ∃ (T : Sylow 2 A) (hzT : (⟨z, hzA⟩ : A) ∈ (T : Subgroup A)),
      (T : Subgroup A) =
        (P : Subgroup (Subgroup.centralizer ({(⟨z, hzA⟩ : A)} : Set A))).map
          (Subgroup.centralizer ({(⟨z, hzA⟩ : A)} : Set A)).subtype ∧
      (⟨(⟨z, hzA⟩ : A), hzT⟩ : (T : Subgroup A)) ∈ Subgroup.center (T : Subgroup A) := by
  apply centralizer_sylow_of_odd_point_class
  · simpa only [Subgroup.orderOf_mk] using h.distinguished_order
  · exact subgroup_full_class_card_odd h hzA hescapeA S hzS hzcenter

theorem involution_point_subgroup_inheritance [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (A : Subgroup G) (hzA : z ∈ A) (hescapeA : ¬ A ≤ H) :
    InvolutionPointLocalEmbedding (H.subgroupOf A) (⟨z, hzA⟩ : A) ∧
      ((∃ (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G)),
        (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) →
       ∃ (T : Sylow 2 A) (hzT : (⟨z, hzA⟩ : A) ∈ (T : Subgroup A)),
        (⟨(⟨z, hzA⟩ : A), hzT⟩ : (T : Subgroup A)) ∈ Subgroup.center (T : Subgroup A)) := by
  refine ⟨local_datum_subgroup_inheritance h A hzA hescapeA, ?_⟩
  rintro ⟨S, hzS, hzcenter⟩
  let P : Sylow 2 (Subgroup.centralizer ({(⟨z, hzA⟩ : A)} : Set A)) :=
    Classical.choice inferInstance
  obtain ⟨T, hzT, _, hcenter⟩ :=
    subgroup_centralizer_sylow_is_ambient h hzA hescapeA S hzS hzcenter P
  exact ⟨T, hzT, hcenter⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
