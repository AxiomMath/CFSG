module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5pk_isSubnormal_sup {X K O : Subgroup G} (hKX : K ≤ X) (hOX : O ≤ X)
    (hK : (K.subgroupOf X).IsSubnormal) (hO : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O) :
    ((K ⊔ O).subgroupOf X).IsSubnormal := by
  let N : Subgroup ↥X := O.subgroupOf X
  let K' : Subgroup ↥X := K.subgroupOf X
  have hN : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOX]
    exact fun h k hh hk => hO k hk h hh
  haveI : N.Normal := hN
  have hEq : (K ⊔ O).subgroupOf X = K' ⊔ N := Subgroup.subgroupOf_sup hKX hOX
  rw [hEq]
  have hmap : (K'.map (QuotientGroup.mk' N)).IsSubnormal :=
    hK.map (QuotientGroup.mk'_surjective N)
  have hcomap := hmap.comap (QuotientGroup.mk' N)
  rwa [Subgroup.comap_map_eq (f := QuotientGroup.mk' N) K',
    QuotientGroup.ker_mk'] at hcomap

theorem sec5pk_isSubnormal_of_normal {X M A : Subgroup G} (hAM : A ≤ M) (hMX : M ≤ X)
    (hA : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hM : (M.subgroupOf X).IsSubnormal) :
    (A.subgroupOf X).IsSubnormal := by
  let A' : Subgroup ↥X := A.subgroupOf X
  let M' : Subgroup ↥X := M.subgroupOf X
  have hle : A' ≤ M' := Subgroup.subgroupOf_mono X hAM
  have hN : (A'.subgroupOf M').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro a m ha hm
    have ha' : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hm' : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    change (m * a * m⁻¹) ∈ A.subgroupOf X
    rw [Subgroup.mem_subgroupOf]
    simpa using hA (m : G) hm' (a : G) ha'
  have hsub : A'.IsSubnormal := Subgroup.IsSubnormal.step A' M' hle hM hN
  exact hsub

theorem sec5pk_cent_normal {M O R : Subgroup G}
    (hOc : ∀ o ∈ O, ∀ m ∈ M, m * o * m⁻¹ = o)
    (hdec : ∀ m ∈ M, ∃ c ∈ M ⊓ centralizer (R : Set G), c⁻¹ * m ∈ O) :
    ∀ m ∈ M, ∀ c ∈ M ⊓ centralizer (R : Set G), m * c * m⁻¹ ∈ M ⊓ centralizer (R : Set G) := by
  intro m hm c hc
  obtain ⟨c₀, hc₀, ho⟩ := hdec m hm
  refine ⟨M.mul_mem (M.mul_mem hm hc.1) (M.inv_mem hm), ?_⟩
  have hoc : (c₀⁻¹ * m) * c = c * (c₀⁻¹ * m) := by
    have h := hOc (c₀⁻¹ * m) ho c hc.1
    calc (c₀⁻¹ * m) * c = (c * (c₀⁻¹ * m) * c⁻¹) * c := by rw [h]
      _ = c * (c₀⁻¹ * m) := by group
  have hconj : m * c * m⁻¹ = c₀ * c * c₀⁻¹ := by
    have hm' : m = c₀ * (c₀⁻¹ * m) := by group
    rw [hm']
    calc c₀ * (c₀⁻¹ * m) * c * (c₀ * (c₀⁻¹ * m))⁻¹
        = c₀ * ((c₀⁻¹ * m) * c * (c₀⁻¹ * m)⁻¹) * c₀⁻¹ := by group
      _ = c₀ * c * c₀⁻¹ := by rw [hoc]; group
  rw [hconj]
  exact (centralizer (R : Set G)).mul_mem
    ((centralizer (R : Set G)).mul_mem hc₀.2 hc.2)
    ((centralizer (R : Set G)).inv_mem hc₀.2)

end CFSG.OddStandard.SmallF3.Omega
