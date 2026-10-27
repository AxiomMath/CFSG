module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End8c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB4
public import Certificates.Data.ExceptionalSL3

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem isSubnormal_comap {H X : Type*} [Group H] [Group X] (α : H →* X) {B : Subgroup X}
    (hB : B.IsSubnormal) : (B.comap α).IsSubnormal := by
  exact Subgroup.IsSubnormal.comap α hB

theorem caseA_pocket {H X : Type} [Group H] [Finite H] [Group X] {z : H} (hz : z ∈ center H)
    (hz2 : orderOf z = 2) (α : H →* X) (hα : Function.Surjective α) (hker : α.ker = zpowers z)
    {K : Subgroup H} (hK : Nonempty (↥K ≃* SL(2, ZMod 3))) (hzK : z ∈ K) {Nn : Subgroup X}
    [Nn.Normal] (hodd : Odd (Nat.card Nn)) (hsub : (K.map α ⊔ Nn).IsSubnormal) :
    ∃ P : Subgroup H, z ∈ P ∧ P.IsSubnormal ∧ IsSL2qMod P 3 1 := by
  let P : Subgroup H := (K.map α ⊔ Nn).comap α
  let R : Subgroup H := Nn.comap α
  have hzker : z ∈ α.ker := by rw [hker]; exact Subgroup.mem_zpowers z
  have hαz : α z = 1 := MonoidHom.mem_ker.mp hzker
  have hzP : z ∈ P := by
    rw [Subgroup.mem_comap, hαz]
    exact Subgroup.one_mem _
  have hzR : z ∈ R := by
    rw [Subgroup.mem_comap, hαz]
    exact Subgroup.one_mem _
  have hRnorm : R.Normal := Subgroup.normal_comap α
  have hKP : K ≤ P := by
    intro k hk
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem α hk)
  have hRP : R ≤ P := by
    intro r hr
    rw [Subgroup.mem_comap] at hr ⊢
    exact Subgroup.mem_sup_right hr
  have hKR : K ⊔ R = P := by
    apply le_antisymm
    · exact sup_le hKP hRP
    · intro x hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨y, hy, n, hn, hyn⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := K.map α) (t := Nn)).mp hx
      obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hy
      have hxR : k⁻¹ * x ∈ R := by
        rw [Subgroup.mem_comap]
        have h1 : α (k⁻¹ * x) = n := by
          rw [map_mul, map_inv, ← hyn]
          group
        rw [h1]
        exact hn
      have hmem := Subgroup.mul_mem_sup hkK hxR
      rwa [mul_inv_cancel_left] at hmem
  have hzcenter : (⟨z, hzP⟩ : ↥P) ∈ center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (g : H))
  have hz2' : orderOf (⟨z, hzP⟩ : ↥P) = 2 := by
    rw [Subgroup.orderOf_mk z hzP, hz2]
  have hK' : Nonempty (↥(K.subgroupOf P) ≃* SL(2, ZMod 3)) :=
    hK.map fun e => (Subgroup.subgroupOfEquivOfLe hKP).trans e
  have hzK' : (⟨z, hzP⟩ : ↥P) ∈ K.subgroupOf P := hzK
  have hzR' : (⟨z, hzP⟩ : ↥P) ∈ R.subgroupOf P := hzR
  haveI : (R.subgroupOf P).Normal := hRnorm.subgroupOf P
  have hKR' : K.subgroupOf P ⊔ R.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKP hRP, hKR, Subgroup.subgroupOf_self]
  have hcardR : Nat.card (R.subgroupOf P) = 2 * Nat.card Nn := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv]
    have hcardker : Nat.card (α.comp R.subtype).ker = 2 := by
      rw [← MonoidHom.comap_ker α R.subtype, hker]
      change Nat.card ((zpowers z).subgroupOf R) = 2
      rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le_of_mem hzR)).toEquiv,
        Nat.card_zpowers, hz2]
    have hrange : (α.comp R.subtype).range = Nn := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective hα Nn
    have h := Subgroup.card_ker_mul_card_range (α.comp R.subtype)
    rw [hcardker, hrange] at h
    exact h.symm
  refine ⟨P, hzP, isSubnormal_comap α hsub, ?_⟩
  unfold IsSL2qMod
  exact sl2_quotient_of_sup hzcenter hz2' (K.subgroupOf P) (R.subgroupOf P) hK' hzK' hzR'
    hcardR hodd hKR'

end CFSG.OddStandard.SmallF3.Omega
