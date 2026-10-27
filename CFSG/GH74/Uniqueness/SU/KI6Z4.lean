module

public import CFSG.GH74.Uniqueness.SU.KI6Z4Core
public import CFSG.GH74.Uniqueness.SU.KI6A9Final

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG

theorem ki6Z4_of_QPCC
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification) : KI6Z4 := by
  intro H _ _ T H₀ h L hL hrank hZ4
  obtain ⟨hLn, -, -, hrk, TL, hTL, hΓL, hDlt⟩ := h.rank2_component hL hrank
  have := hLn
  have hZp := h.isPGroup_center_component hL
  have hperf : Group.IsPerfect ↥L := hL.1.1
  have hZrank : Open.twoRank ↥(center ↥L) ≤ 1 := by
    let g : ↥(center ↥L) →* H := L.subtype.comp (center ↥L).subtype
    have hginj : Function.Injective g := L.subtype_injective.comp (center ↥L).subtype_injective
    have h1 := SU4.pRank_map_of_injective g hginj (⊤ : Subgroup ↥(center ↥L))
    have h2 : (⊤ : Subgroup ↥(center ↥L)).map g ≤ centralizer (L : Set H) := by
      rintro _ ⟨z, -, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩)
    have h3 := SU1.pRank_mono (p := 2) (by norm_num) h2
    unfold Open.twoRank
    omega
  have hcyc : IsCyclic ↥(center ↥L) := by
    let : CommGroup ↥(center ↥L) :=
      { (inferInstance : Group ↥(center ↥L)) with
        mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
    exact CFSG.TwoRankLowerBound.Helpers.abelian_rank_one_two_group_isCyclic ↥(center ↥L) hZp
      hZrank
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  have hrankL : 2 ≤ Open.twoRank ↥L := by
    have h1 := SU4.pRank_map_of_injective L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
    have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [Subgroup.map_top]; exact Subgroup.range_subtype _
    rw [h2] at h1
    unfold Open.twoRank
    omega
  have hTLle : (TL : Subgroup ↥L) ≤ H₀.subgroupOf L := by
    intro x hx
    have hx' : (x : H) ∈ (T : Subgroup H) ⊓ L := by rw [← hTL]; exact ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (h.sylow_le hx'.1)
  exact z4_core hQ hL.1.2.1 (c := (c : ↥L)) c.2
    (fun z hz => by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hc ⟨z, hz⟩)
      exact mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩)
    hZp hZ4 hrankL TL (H₀.subgroupOf L) hTLle hDlt.ne hΓL

theorem ki6_of_QPCC'
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification) : K.KI6 :=
  ki6_of_QPCC_Z4 hQ (ki6Z4_of_QPCC hQ)

end CFSG.GH74.Uniqueness.SU.K.R6
