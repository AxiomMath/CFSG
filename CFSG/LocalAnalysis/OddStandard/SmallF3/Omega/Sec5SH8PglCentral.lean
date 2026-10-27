module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8D8
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5sh8_central_mem_of_index_two {X : Type} [Group X] (P : Subgroup X)
    (hP : Nonempty (↥P ≃* DihedralGroup 4)) (J : Subgroup X) (hJ : J.index = 2) :
    ∀ z ∈ P, (∀ g ∈ P, z * g = g * z) → z ∈ J := by
  intro z hzP hzcent
  by_contra hzJ
  haveI hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ
  let zP : ↥P := ⟨z, hzP⟩
  have hzPcoe : (zP : X) = z := rfl
  have hzcentP : ∀ g : ↥P, zP * g = g * zP := by
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hzPcoe]
    exact hzcent (g : X) g.2
  have hNpindex : (J.subgroupOf P).index = 2 := by
    change (J.comap P.subtype).index = 2
    rw [Subgroup.index_comap, Subgroup.range_subtype]
    have hsup : J.relIndex P = J.relIndex (P ⊔ J) :=
      (Subgroup.relIndex_sup_right (H := P) (K := J)).symm
    rw [hsup]
    have hdvd : J.relIndex (P ⊔ J) ∣ 2 := by
      simpa [hJ] using
        Subgroup.relIndex_dvd_index_of_le (H := J) (K := P ⊔ J) le_sup_right
    have hne1 : J.relIndex (P ⊔ J) ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hzJ (h1 (Subgroup.mem_sup_left hzP))
    rcases Nat.prime_two.eq_one_or_self_of_dvd (J.relIndex (P ⊔ J)) hdvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  have hcardP : Nat.card ↥P = 8 := by
    obtain ⟨e⟩ := hP
    calc Nat.card ↥P = Nat.card (DihedralGroup 4) := Nat.card_congr e.toEquiv
      _ = 2 * 4 := DihedralGroup.nat_card
      _ = 8 := by norm_num
  have hcardNp : Nat.card ↥(J.subgroupOf P) = 4 := by
    have h := Subgroup.card_mul_index (H := J.subgroupOf P)
    rw [hNpindex, hcardP] at h
    omega
  haveI hNpcomm : IsMulCommutative ↥(J.subgroupOf P) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by
      rw [hcardNp]; norm_num)
  have hdecomp : ∀ a : ↥P, a ∈ J.subgroupOf P ∨ zP * a ∈ J.subgroupOf P := by
    intro a
    by_cases haJ : (a : X) ∈ J
    · left
      rw [Subgroup.mem_subgroupOf]
      exact haJ
    · right
      rw [Subgroup.mem_subgroupOf]
      have hiff : z ∈ J ↔ (a : X) ∈ J :=
        ⟨fun h => absurd h hzJ, fun h => absurd h haJ⟩
      have hzmem : z * (a : X) ∈ J := (Subgroup.mul_mem_iff_of_index_two hJ).mpr hiff
      simpa [Subgroup.coe_mul, hzPcoe] using hzmem
  let k : Set ↥P := {zP} ∪ (J.subgroupOf P : Set ↥P)
  have hk : k = {zP} ∪ (J.subgroupOf P : Set ↥P) := rfl
  have hkcomm : k.Pairwise Commute := by
    intro x hx y hy hxy
    rw [hk, Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact (commute_iff_eq zP y).mpr (hzcentP y)
    · rcases hy with rfl | hy
      · exact (commute_iff_eq x zP).mpr (hzcentP x).symm
      · exact (commute_iff_eq x y).mpr (setLike_mul_comm hx hy)
  haveI hclosurecomm : IsMulCommutative (Subgroup.closure k) :=
    Subgroup.isMulCommutative_closure hkcomm
  have hzk : zP ∈ Subgroup.closure k :=
    Subgroup.subset_closure (by rw [hk]; simp)
  have hclosureTop : Subgroup.closure k = ⊤ := by
    refine le_antisymm le_top ?_
    intro a _
    rcases hdecomp a with ha | ha
    · exact Subgroup.subset_closure (by rw [hk]; exact Set.mem_union_right _ ha)
    · have h2 : zP * a ∈ Subgroup.closure k :=
        Subgroup.subset_closure (by rw [hk]; exact Set.mem_union_right _ ha)
      have h1 : zP⁻¹ ∈ Subgroup.closure k := Subgroup.inv_mem _ hzk
      have h3 : zP⁻¹ * (zP * a) ∈ Subgroup.closure k := Subgroup.mul_mem _ h1 h2
      simpa using h3
  obtain ⟨a, haP, b, hbP, hab⟩ := sec5sh8_d8_not_comm P hP
  have haCl : (⟨a, haP⟩ : ↥P) ∈ Subgroup.closure k := by rw [hclosureTop]; simp
  have hbCl : (⟨b, hbP⟩ : ↥P) ∈ Subgroup.closure k := by rw [hclosureTop]; simp
  have hmul : (⟨a, haP⟩ : ↥P) * (⟨b, hbP⟩ : ↥P) =
      (⟨b, hbP⟩ : ↥P) * (⟨a, haP⟩ : ↥P) := setLike_mul_comm haCl hbCl
  exact hab (by simpa using congrArg Subtype.val hmul)

end CFSG.OddStandard.SmallF3.Omega
