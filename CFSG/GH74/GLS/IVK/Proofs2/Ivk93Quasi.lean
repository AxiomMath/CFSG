module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open scoped commutatorElement

theorem ivk93x_commutatorElement_central_mul {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (x y : Q) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * (w * y) * (z * x)⁻¹ * (w * y)⁻¹
      = z * (x * w * y * x⁻¹) * z⁻¹ * y⁻¹ * w⁻¹ := by group
    _ = (x * w * y * x⁻¹) * z * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← hz' (x * w * y * x⁻¹)]
    _ = (w * x * y * x⁻¹ * y⁻¹) * w⁻¹ := by rw [hw' x]; group
    _ = w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * w * w⁻¹ := by rw [← hw' (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem ivk93x_isSubnormal_le_center_or_eq_top {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {S : Subgroup Q} (hS : S.IsSubnormal) : S ≤ Subgroup.center Q ∨ S = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have h1 : (S.map (QuotientGroup.mk' (Subgroup.center Q))).IsSubnormal :=
    hS.map (QuotientGroup.mk'_surjective _)
  rcases h1.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · right
    have hsup : S ⊔ Subgroup.center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) S
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hle : commutator Q ≤ S := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ S ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top x
      have hy : y ∈ S ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top y
      obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
        rw [Subgroup.mem_center_iff.mp hz n, Subgroup.mem_center_iff.mp hz' n']
        exact ivk93x_commutatorElement_central_mul hz hz' n n'
      rw [e, commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hn hn') (S.inv_mem hn)) (S.inv_mem hn')
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

theorem ivk93x_eq_centralizer_of_pComp {J : Type} [Group J] {x : J} {L : Subgroup J}
    (hL : IsPCompIn 2 (centralizer ({x} : Set J)) L) (hns : ¬ Group.IsSolvable ↥L)
    (hq : CFSG.IsQuasisimple ↥(centralizer ({x} : Set J))) : L = centralizer ({x} : Set J) := by
  obtain ⟨hle, hcomp⟩ := hL
  obtain ⟨-, -, hs, -, -⟩ := id hcomp
  rcases ivk93x_isSubnormal_le_center_or_eq_top hq hs with hc | htop
  · exfalso
    apply hns
    refine Group.isSolvable_of_comm (fun a b => ?_)
    have ha : (⟨(a : J), hle a.2⟩ : ↥(centralizer ({x} : Set J))) ∈
        Subgroup.center ↥(centralizer ({x} : Set J)) := hc (Subgroup.mem_subgroupOf.mpr a.2)
    exact Subtype.ext (congrArg Subtype.val ((Subgroup.mem_center_iff.mp ha) ⟨(b : J), hle b.2⟩)).symm
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

namespace Ivk93Cfg

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {L₁ L₂ : Subgroup J}

theorem false_of_quasisimple_centralizer (h : Ivk93Cfg x q L₁ L₂)
    (hq : CFSG.IsQuasisimple ↥(centralizer ({x} : Set J))) : False :=
  h.ne ((ivk93x_eq_centralizer_of_pComp h.comp₁ h.not_solvable₁ hq).trans
    (ivk93x_eq_centralizer_of_pComp h.comp₂ h.symm.not_solvable₁ hq).symm)

end Ivk93Cfg

end CFSG.GH74.GLS.IVK.Proofs2
