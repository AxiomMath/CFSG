module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.Nilpotent

public section

open Subgroup

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {T H M : Subgroup G}

theorem isSylowOf_of_normalizer_inf_le (hT : IsSylowOf p T (H ⊓ M))
    (hN : Subgroup.normalizer (T : Set G) ⊓ M ≤ H) : IsSylowOf p T M := by
  classical
  by_contra hTM
  have hTle : T ≤ M := hT.le.trans inf_le_right
  have hTsub : IsPGroup p (T.subgroupOf M) := hT.isPGroup.comap_subtype
  obtain ⟨S, hTS⟩ := hTsub.exists_le_sylow
  let Sg : Subgroup G := (S : Subgroup M).map M.subtype
  have hTSg : T ≤ Sg := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTle]
    exact Subgroup.map_mono hTS
  have hSgle : Sg ≤ M := Subgroup.map_subtype_le _
  have hSgp : IsPGroup p Sg := S.isPGroup'.map M.subtype
  have hne : Sg ≠ T := by
    intro heq
    apply hTM
    have hSyl : IsSylowOf p Sg M := ⟨S, rfl⟩
    rwa [heq] at hSyl
  have hlt : T < Sg := lt_of_le_of_ne hTSg (Ne.symm hne)
  haveI : Group.IsNilpotent Sg := hSgp.isNilpotent
  have hnc : NormalizerCondition Sg := Group.normalizerCondition_of_isNilpotent
  have hlt' : T.subgroupOf Sg < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have hSgT : Sg ≤ T := by
      intro y hy
      have hy' : (⟨y, hy⟩ : Sg) ∈ T.subgroupOf Sg := by
        rw [htop]
        trivial
      exact Subgroup.mem_subgroupOf.mp hy'
    exact hne (le_antisymm hSgT hTSg)
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (hnc (T.subgroupOf Sg) hlt')
  have hxS : (x : G) ∈ Sg := x.2
  have hxnorm : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have hx : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf Sg := by
      rw [Subgroup.subgroupOf_normalizer_eq hTSg]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hx
  have hxnotT : (x : G) ∉ T := fun hx => hxT (Subgroup.mem_subgroupOf.mpr hx)
  have hxHM : (x : G) ∈ H ⊓ M := ⟨hN ⟨hxnorm, hSgle hxS⟩, hSgle hxS⟩
  have hZp : IsPGroup p (Subgroup.zpowers (x : G)) :=
    hSgp.to_le (Subgroup.zpowers_le.mpr hxS)
  have hZnorm : Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hxnorm
  have hsupP : IsPGroup p (T ⊔ Subgroup.zpowers (x : G) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hT.isPGroup hZp hZnorm
  have hsupLe : (T ⊔ Subgroup.zpowers (x : G) : Subgroup G) ≤ H ⊓ M :=
    sup_le hT.le (Subgroup.zpowers_le.mpr hxHM)
  have heq : (T ⊔ Subgroup.zpowers (x : G) : Subgroup G) = T :=
    hT.eq_of_le le_sup_left hsupLe hsupP
  exact hxnotT (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G)))

end CFSG.ABGLocalTools
