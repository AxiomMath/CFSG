module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Facts
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rightConjugate_subgroupOf {X C : Subgroup G} (h : ↥C) :
    rightConjugate (X.subgroupOf C) h = (rightConjugate X (h : G)).subgroupOf C := by
  ext y
  simp only [mem_rightConjugate_iff, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite G] in
theorem rightConjugate_le_of_le {X C : Subgroup G} (hXC : X ≤ C) {h : G} (hh : h ∈ C) :
    rightConjugate X h ≤ C := by
  intro y hy
  rw [mem_rightConjugate_iff] at hy
  have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
  rw [this]
  exact C.mul_mem (C.mul_mem (C.inv_mem hh) (hXC hy)) hh

theorem Hyp19.hyp19K {z : G} {X T : Subgroup G} (hH : Hyp19 G z X T) :
    Hyp19K ↥(centralizer ({z} : Set G))
      ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
      (X.subgroupOf (centralizer ({z} : Set G))) (T.subgroupOf (centralizer ({z} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  have hE : ExtraIn X z := ⟨hH.extraspecial, hH.order, hH.sylow⟩
  have hzX := hE.mem
  have hCX : centralizer (X : Set G) ≤ C := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy z hzX).symm
  have hTC : T ≤ C := hH.sylowT.le
  have hzmap : (zpowers (⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥C)).map C.subtype =
      zpowers z := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hcmap : (centralizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C)).map C.subtype =
      centralizer (X : Set G) := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact mem_centralizer_iff.mpr fun x hx => congrArg Subtype.val
        (mem_centralizer_iff.mp hy' ⟨x, hH.le hx⟩ (mem_subgroupOf.mpr hx))
    · intro hy
      exact ⟨⟨y, hCX hy⟩, mem_centralizer_iff.mpr fun x hx =>
        Subtype.ext (mem_centralizer_iff.mp hy x (mem_subgroupOf.mp hx)), rfl⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, fun x hx => mem_subgroupOf.mpr (hH.le_T (mem_subgroupOf.mp hx)),
    ?_, ?_⟩
  · exact mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  · exact CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (subgroupOfEquivOfLe hH.le).symm hH.extraspecial
  · rw [Subgroup.orderOf_mk]
    exact hH.order
  · rw [← isSylowOf_map_subtype_iff C, hzmap, hcmap]
    exact hH.sylow
  · rw [← isSylowOf_map_subtype_iff C, subgroupOf_map_subtype, inf_eq_left.mpr hTC,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hH.sylowT
  · intro h hle
    rw [rightConjugate_subgroupOf] at hle ⊢
    have hle' : rightConjugate X (h : G) ≤ T := fun y hy => by
      have := hle (mem_subgroupOf.mpr (show ((⟨y, rightConjugate_le_of_le hH.le h.2 hy⟩ : ↥C) :
        G) ∈ rightConjugate X (h : G) from hy))
      exact mem_subgroupOf.mp this
    rw [hH.weak h h.2 hle']
  · intro h hrank
    rw [rightConjugate_subgroupOf] at hrank ⊢
    have hmap : (X.subgroupOf C ⊓ (rightConjugate X (h : G)).subgroupOf C).map C.subtype =
        X ⊓ rightConjugate X (h : G) := by
      have h0 : X.subgroupOf C ⊓ (rightConjugate X (h : G)).subgroupOf C =
          (X ⊓ rightConjugate X (h : G)).subgroupOf C := by
        ext y
        simp [mem_subgroupOf]
      rw [h0, subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_left.trans hH.le)]
    have h1 := CFSG.SectionRank.pRank_le_map one_lt_two C.subtype C.subtype_injective
      (X.subgroupOf C ⊓ (rightConjugate X (h : G)).subgroupOf C)
    rw [hmap] at h1
    rw [hH.rank h h.2 (lt_of_lt_of_le hrank h1)]

end Transfer

theorem step110_of (hT : Tim77Lemma24) : Step110 := by
  intro G _ _ z X T hH x hx h hh hxT
  by_contra hxX
  have hK := hH.hyp19K
  have := zpowers_normal_of_mem_center hK.center
  have hxC : x ∈ centralizer ({z} : Set G) := hH.le hx
  obtain ⟨g, hg⟩ := hK.exists_tim77 hT (x := ⟨x, hxC⟩) (h := ⟨h, hh⟩) (mem_subgroupOf.mpr hx)
    (mem_subgroupOf.mpr (by simpa using hxT)) (fun h' => hxX (by simpa using mem_subgroupOf.mp h'))
  have hX128 : 128 ≤ Nat.card (X.subgroupOf (centralizer ({z} : Set G))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hH.le).toEquiv]
    rcases hH.card with h7 | h9
    · rw [h7]; norm_num
    · rw [h9]; norm_num
  exact hK.false_of_tim77Facts hX128 hg

end CFSG.ComponentClassification.AS81
