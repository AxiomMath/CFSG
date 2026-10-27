module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_intersection_eq (Q Y : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (heven : Even (Nat.card (Q.subgroupOf Y))) :
    Subgroup.normalizer (Q.subgroupOf Y : Set Y) =
      (Subgroup.normalizer (Q : Set G)).subgroupOf Y := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q.subgroupOf Y) 2
    (even_iff_two_dvd.mp heven)
  have hzQ : ((z : Y) : G) ∈ Q := z.property
  have hzG : orderOf ((z : Y) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  ext a
  constructor
  · intro ha
    have hconj : a * (z : Y) * a⁻¹ ∈ Q.subgroupOf Y :=
      (Subgroup.mem_normalizer_iff.mp ha (z : Y)).mp z.property
    have hconjG : (a : G) * ((z : Y) : G) * (a : G)⁻¹ ∈ Q := hconj
    have hinverse : (a : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (involution_conjugate_mem_Q_iff Q hodd ((z : Y) : G) hzQ hzG
        (a : G)⁻¹).mp (by simpa only [inv_inv] using hconjG)
    exact (Subgroup.normalizer (Q : Set G)).inv_mem_iff.mp hinverse
  · intro ha
    apply Subgroup.mem_normalizer_iff.mpr
    intro t
    exact Subgroup.mem_normalizer_iff.mp ha (t : G)

omit [Finite G] in
theorem right_conjugate_intersection_subtype (Q Y : Subgroup G) (g : Y) :
    (rightConjugate (Q.subgroupOf Y) g).map Y.subtype =
      rightConjugate Q (g : G) ⊓ Y := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(mem_rightConjugate_iff Q g t).mpr
      ((mem_rightConjugate_iff (Q.subgroupOf Y) g t).mp ht), t.property⟩
  · rintro ⟨hx, hxY⟩
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    apply (mem_rightConjugate_iff (Q.subgroupOf Y) g _).mpr
    exact (mem_rightConjugate_iff Q g x).mp hx

theorem tightly_embedded_intersection (Q Y : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (heven : Even (Nat.card (Q.subgroupOf Y))) :
    TightlyEmbedded (Q.subgroupOf Y) := by
  refine ⟨heven, ?_⟩
  intro g hg
  have houtside : (g : G) ∉ Subgroup.normalizer (Q : Set G) := by
    intro hgH
    apply hg
    rw [normalizer_intersection_eq Q Y hodd heven]
    exact hgH
  have hle : ((Q.subgroupOf Y) ⊓ rightConjugate (Q.subgroupOf Y) g).map
      Y.subtype ≤ Q ⊓ rightConjugate Q (g : G) := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨ht.1, ?_⟩
    exact (mem_rightConjugate_iff Q g t).mpr
      ((mem_rightConjugate_iff (Q.subgroupOf Y) g t).mp ht.2)
  have hcard := (htight.2 g houtside).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rwa [Subgroup.card_subtype] at hcard

theorem odd_normalizer_overlaps_intersection (Q Y : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (heven : Even (Nat.card (Q.subgroupOf Y))) :
    OddNormalizerOverlaps (Q.subgroupOf Y) := by
  intro g hg
  have houtside : (g : G) ∉ Subgroup.normalizer (Q : Set G) := by
    intro hgH
    apply hg
    rw [normalizer_intersection_eq Q Y hodd heven]
    exact hgH
  have hle : (rightConjugate (Q.subgroupOf Y) g ⊓
      Subgroup.normalizer (Q.subgroupOf Y : Set Y)).map Y.subtype ≤
      rightConjugate Q (g : G) ⊓ Subgroup.normalizer (Q : Set G) := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (mem_rightConjugate_iff Q g t).mpr
        ((mem_rightConjugate_iff (Q.subgroupOf Y) g t).mp ht.1)
    · rw [normalizer_intersection_eq Q Y hodd heven] at ht
      exact ht.2
  have hcard := (hodd g houtside).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rwa [Subgroup.card_subtype] at hcard

theorem normal_intersection_iff_le_normalizer (Q Y : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (heven : Even (Nat.card (Q.subgroupOf Y))) :
    (Q.subgroupOf Y).Normal ↔ Y ≤ Subgroup.normalizer (Q : Set G) := by
  rw [← Subgroup.normalizer_eq_top_iff, normalizer_intersection_eq Q Y hodd heven]
  exact Subgroup.subgroupOf_eq_top

end CFSG.ComponentClassification.AschbacherTightEmbedding
