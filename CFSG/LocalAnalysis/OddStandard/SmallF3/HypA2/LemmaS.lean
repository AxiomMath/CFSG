module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem le_normalizer_of_noncentral {G : Type} [Group G] [Finite G] {y z : G} {K : Subgroup G}
    (hK : Omega.IsComponentIn K (centralizer ({y} : Set G))) (hzK : z ∈ K)
    (hzZ : z ∉ (center ↥K).map K.subtype) :
    centralizer ({y, z} : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  have hsub : ({y} : Set G) ⊆ {y, z} := by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact Set.mem_insert y {z}
  have hgy : g ∈ centralizer ({y} : Set G) := Subgroup.centralizer_le hsub hg
  have hKg : Omega.IsComponentIn (K.map (MulAut.conj g).toMonoidHom)
      (centralizer ({y} : Set G)) := hK.map_conj hgy
  have hgz : g * z = z * g := (Subgroup.mem_centralizer_iff.1 hg z (by simp)).symm
  have hzKg : z ∈ K.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.2 ⟨z, hzK, ?_⟩
    change MulAut.conj g z = z
    rw [MulAut.conj_apply, hgz, mul_assoc, mul_inv_cancel, mul_one]
  have hEq : K.map (MulAut.conj g).toMonoidHom = K := by
    by_contra hne
    have hcomm := hKg.commute_of_ne hK hne
    have hzc : (⟨z, hzK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact (hcomm z hzKg (k : G) k.2).symm
    exact hzZ (Subgroup.mem_map.2 ⟨⟨z, hzK⟩, hzc, rfl⟩)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq

theorem isTwoComponentIn_centralizer_pair {G : Type} [Group G] [Finite G] {y z : G}
    {K T : Subgroup G} (hK : Omega.IsComponentIn K (centralizer ({y} : Set G))) (hzK : z ∈ K)
    (hzZ : z ∉ (center ↥K).map K.subtype)
    (hT : ComponentClassification.HarrisLit.IsTwoComponentIn T (K ⊓ centralizer ({z} : Set G))) :
    ComponentClassification.HarrisLit.IsTwoComponentIn T (centralizer ({y, z} : Set G)) := by
  refine ⟨?_, ?_, hT.2.2⟩
  ·
    intro t ht
    obtain ⟨htK, htz⟩ := Subgroup.mem_inf.1 (hT.1 ht)
    rw [centralizer_pair_eq_inf]
    exact ⟨hK.1 htK, htz⟩
  ·
    have hNC2 : (K ⊓ centralizer ({z} : Set G)) ≤ centralizer ({y, z} : Set G) := by
      intro x hx
      obtain ⟨hxK, hxz⟩ := Subgroup.mem_inf.1 hx
      rw [centralizer_pair_eq_inf]
      exact ⟨hK.1 hxK, hxz⟩
    have hC2z : centralizer ({y, z} : Set G) ≤ centralizer ({z} : Set G) := by
      rw [centralizer_pair_eq_inf]
      exact inf_le_right
    have hleK : centralizer ({y, z} : Set G) ≤ normalizer (K : Set G) :=
      le_normalizer_of_noncentral hK hzK hzZ
    have hleN : centralizer ({y, z} : Set G) ≤
        normalizer ((K ⊓ centralizer ({z} : Set G)) : Set G) := by
      intro g hg
      refine Subgroup.inf_normalizer_le_normalizer_inf (H := K)
        (K := centralizer ({z} : Set G)) ⟨hleK hg, ?_⟩
      exact Subgroup.le_normalizer (hC2z hg)
    have hNnorm : ((K ⊓ centralizer ({z} : Set G)).subgroupOf
        (centralizer ({y, z} : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNC2).mpr hleN
    have hKsn : ((K ⊓ centralizer ({z} : Set G)).subgroupOf
        (centralizer ({y, z} : Set G))).IsSubnormal := hNnorm.isSubnormal
    refine Subgroup.IsSubnormal.trans
      (Subgroup.subgroupOf_mono (centralizer ({y, z} : Set G)) hT.1) ?_ hKsn
    convert Subgroup.IsSubnormal.comap (Subgroup.subgroupOfEquivOfLe hNC2).toMonoidHom
      hT.2.1 using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl

end CFSG.OddStandard.SmallF3.HypA2
