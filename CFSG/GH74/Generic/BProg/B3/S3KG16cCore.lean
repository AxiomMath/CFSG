module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {Kt : Type} [Group Kt]

theorem isSolvable_centralizer {u : Kt} {S : Subgroup Kt} (huS : u ∈ S)
    (hcomm : ∀ a ∈ centralizer ({u} : Set Kt), ∀ b ∈ centralizer ({u} : Set Kt), ⁅a, b⁆ ∈ S) :
    Group.IsSolvable ↥(centralizer (S : Set Kt)) := by
  set H := centralizer (S : Set Kt) with hH
  have hHu : ∀ a ∈ H, a ∈ centralizer ({u} : Set Kt) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact mem_centralizer_iff.mp ha u huS
  have hle : commutator ↥H ≤ center ↥H := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro c
    have hab : ((⁅a, b⁆ : ↥H) : Kt) ∈ S := hcomm _ (hHu _ a.2) _ (hHu _ b.2)
    exact Subtype.ext (mem_centralizer_iff.mp c.2 _ hab).symm
  rw [Group.isSolvable_def]
  refine ⟨2, ?_⟩
  rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff, Subgroup.commutator_le]
  intro x hx y _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (hle hx) y).symm

theorem isSolvable_of_fixes {S : Subgroup Kt} (Γ : Subgroup (MulAut Kt))
    (hΓ : ∀ γ ∈ Γ, ∀ s ∈ S, γ s = s)
    (hconj : ∀ c ∈ centralizer (S : Set Kt), MulAut.conj c ∈ Γ)
    (hC : Group.IsSolvable ↥(centralizer (S : Set Kt))) (hO : Group.IsSolvable (Outer Kt)) :
    Group.IsSolvable ↥Γ := by
  let f : ↥(centralizer (S : Set Kt)) →* ↥Γ :=
    ((MulAut.conj : Kt →* MulAut Kt).comp (centralizer (S : Set Kt)).subtype).codRestrict Γ
      fun c => hconj c c.2
  let g : ↥Γ →* Outer Kt := (QuotientGroup.mk' (inner Kt)).comp Γ.subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro γ hγ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hγ
  obtain ⟨k, hk⟩ := hγ
  have hk' : MulAut.conj k = (γ : MulAut Kt) := hk
  have hkS : k ∈ centralizer (S : Set Kt) := by
    rw [mem_centralizer_iff]
    intro s hs
    have h := hΓ γ γ.2 s hs
    rw [← hk', MulAut.conj_apply] at h
    calc s * k = k * s * k⁻¹ * k := by rw [h]
      _ = k * s := by group
  exact ⟨⟨k, hkS⟩, Subtype.ext hk'⟩

end CFSG.GH74.Generic.BProg.B3.S3KG
