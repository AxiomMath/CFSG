module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_exists_fixed_class [Finite G] {z : G} {T Q : Subgroup G} (hT : IsPGroup 2 T)
    (hzT : z ∈ T) (hzc : ∀ g ∈ T, g * z = z * g) (hQT : Q ≤ T)
    (hQn : ∀ g ∈ T, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hnt : ∃ q ∈ Q, q ∉ zpowers z) :
    ∃ p ∈ Q, p ∉ zpowers z ∧ ∀ g ∈ T, g * p * g⁻¹ * p⁻¹ ∈ zpowers z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  let Z' : Subgroup T := (zpowers z).subgroupOf T
  have hZ'le : zpowers z ≤ T := Subgroup.zpowers_le.mpr hzT
  have hZ'normal : Z'.Normal := by
    show ((zpowers z).subgroupOf T).Normal
    rw [Subgroup.normal_subgroupOf_iff hZ'le]
    intro h k hh hk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hkz : k * z * k⁻¹ = z := by
      rw [hzc k hk, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hn, ← conj_zpow, hkz]
    exact Subgroup.zpow_mem_zpowers z n
  haveI : Z'.Normal := hZ'normal
  let π : T →* T ⧸ Z' := QuotientGroup.mk' Z'
  let Q' : Subgroup T := Q.subgroupOf T
  have hQ'normal : Q'.Normal := by
    show (Q.subgroupOf T).Normal
    rw [Subgroup.normal_subgroupOf_iff hQT]
    intro h k hh hk
    exact hQn k hk h hh
  haveI : Q'.Normal := hQ'normal
  let Q'' : Subgroup (T ⧸ Z') := Q'.map π
  have hQ''normal : Q''.Normal := hQ'normal.map π (QuotientGroup.mk'_surjective Z')
  haveI : Q''.Normal := hQ''normal
  have hQ''ne : Q'' ≠ ⊥ := by
    obtain ⟨q, hqQ, hqnot⟩ := hnt
    intro hbot
    have hmem : π ⟨q, hQT hqQ⟩ ∈ Q'' :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hqQ)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hz : (⟨q, hQT hqQ⟩ : T) ∈ Z' := (QuotientGroup.eq_one_iff _).mp hmem
    exact hqnot (Subgroup.mem_subgroupOf.mp hz)
  have hcenter : Q'' ⊓ center (T ⧸ Z') ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hQ''ne
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  have hwQ : (w : T ⧸ Z') ∈ Q'' := w.2.1
  have hwC : (w : T ⧸ Z') ∈ center (T ⧸ Z') := w.2.2
  have hwne' : (w : T ⧸ Z') ≠ 1 := fun h => hwne (Subtype.ext h)
  obtain ⟨x, hxQ', hxw⟩ := Subgroup.mem_map.mp hwQ
  have hxQ : x.1 ∈ Q := Subgroup.mem_subgroupOf.mp hxQ'
  have hxnot : x.1 ∉ zpowers z := by
    intro hx
    have hxZ : x ∈ Z' := Subgroup.mem_subgroupOf.mpr hx
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff (N := Z') x).mpr hxZ
    rw [hxw] at hx1
    exact hwne' hx1
  refine ⟨x.1, hxQ, hxnot, ?_⟩
  intro g hg
  let g' : T := ⟨g, hg⟩
  have hcomm : π g' * π x = π x * π g' := by
    have hcw := Subgroup.mem_center_iff.mp hwC (π g')
    rw [← hxw] at hcw
    exact hcw
  have h1 : π (g' * x * g'⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm,
      mul_assoc (π x) (π g') ((π g')⁻¹), mul_inv_cancel, mul_one, mul_inv_cancel]
  have hmemZ : g' * x * g'⁻¹ * x⁻¹ ∈ Z' :=
    (QuotientGroup.eq_one_iff (N := Z') _).mp h1
  have hfin := Subgroup.mem_subgroupOf.mp hmemZ
  simpa using hfin

end CFSG.OddStandard.SmallF3.Omega
