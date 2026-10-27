module

public import CFSG.GF2Type.CenterFour.CaseDefs
public import CFSG.GF2Type.CenterFour.SettingConj
public import CFSG.GF2Type.CenterFour.BasicFusion

import CFSG.GF2Type.CenterFour.BasicIndex

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem caseA_mem_conj_iff {H : Subgroup G} {g y : G} :
    y ∈ CFSG.conjugate H g ↔ g * y * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem caseA_fused_conj_left {z w : G} (g : G) (h : Fused z w) :
    Fused z (g * w * g⁻¹) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k * g⁻¹, by rw [← hk]; group⟩

private theorem caseA_fused_mul {b a' : G} (hC : Config b n) (ha' : Fused b a')
    (hcomm : a' * b = b * a') (hne : a' ≠ b) : Fused b (b * a') := by
  obtain ⟨k, hk⟩ := ha'
  have hu : k⁻¹ * b * k ∈ centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hk]
    exact hcomm
  have hne' : k⁻¹ * b * k ≠ b := by
    rw [hk]
    exact hne
  obtain ⟨g', hg'⟩ := hC.exists_conj_eq_mul_z hu hne'
  exact ⟨g', by rw [hg', hk]; exact hcomm⟩

theorem CaseA.conj (hC : Config z n) (hA : CaseA z) (g : G) : CaseA (g⁻¹ * z * g) := by
  intro w hw hwu
  have hzw : Fused z (g * w * g⁻¹) := caseA_fused_conj_left g ((fused_conj z g).trans hw)
  have hwz : g * w * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hwu
    calc g * w * g⁻¹ * z = g * (w * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * w) * g⁻¹ := by rw [h1]
      _ = z * (g * w * g⁻¹) := by group
  have hc := Subgroup.mem_centralizer_iff.1 (hA _ hzw hwz)
  rw [centerAt_conj z g, Subgroup.mem_centralizer_iff]
  intro y hy
  have hy2 : y ∈ CFSG.conjugate (centerAt z) g := hy
  have hcy := hc (g * y * g⁻¹) (caseA_mem_conj_iff.1 hy2)
  have key : g * (y * w) * g⁻¹ = g * (w * y) * g⁻¹ := by
    calc g * (y * w) * g⁻¹ = (g * y * g⁻¹) * (g * w * g⁻¹) := by group
      _ = (g * w * g⁻¹) * (g * y * g⁻¹) := hcy
      _ = g * (w * y) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel key)

theorem CaseA.mem_core (hC : Config z n) (hA : CaseA z) {w : G} (hw : Fused z w)
    (hwz : w ∈ centralizer ({z} : Set G)) : w ∈ coreAt z := by
  obtain ⟨g, rfl⟩ := hw
  exact hC.mem_core_of_centralizes g (hA (g⁻¹ * z * g) ⟨g, rfl⟩ hwz)

theorem CaseA.commute_of_commute (hC : Config z n) (hA : CaseA z) {u a a' : G}
    (hu : Fused z u) (huQ : u ∈ coreAt z) (huz : u ≠ z)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (ha' : Fused z a') (ha'Q : a' ∈ coreAt z)
    (hua : u * a = a * u) (hua' : u * a' = a' * u) : a * a' = a' * a := by
  obtain ⟨g, rfl⟩ := hu
  have hC' : Config (g⁻¹ * z * g) n := hC.conj g
  have hA' : CaseA (g⁻¹ * z * g) := CaseA.conj hC hA g
  have hfa : Fused (g⁻¹ * z * g) a := (fused_conj z g).symm.trans ha
  have hfa' : Fused (g⁻¹ * z * g) a' := (fused_conj z g).symm.trans ha'
  have haU : a ∈ coreAt (g⁻¹ * z * g) :=
    CaseA.mem_core hC' hA' hfa (Subgroup.mem_centralizer_singleton_iff.2 hua.symm)
  have ha'U : a' ∈ coreAt (g⁻¹ * z * g) :=
    CaseA.mem_core hC' hA' hfa' (Subgroup.mem_centralizer_singleton_iff.2 hua'.symm)
  have h1 := hC'.comm_eq a haU a' ha'U
  have h2 := hC.comm_eq a haQ a' ha'Q
  by_contra hne
  have hc : ⁅a, a'⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_mul_comm.1 h)
  exact huz ((h1.resolve_left hc).symm.trans (h2.resolve_left hc))

theorem CaseA.mul_mem (hC : Config z n) (hA : CaseA z) {a a' : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (ha' : Fused z a') (ha'Q : a' ∈ coreAt z) (haa' : a * a' = a' * a)
    (hne : a' ≠ a) (hnez : a' ≠ a * z) :
    Fused z (a * a') ∧ a * a' ∈ coreAt z ∧ a * a' ≠ z := by
  have hCa : Config a n := by
    obtain ⟨g, rfl⟩ := ha
    exact hC.conj g
  have hfa : Fused a a' := ha.symm.trans ha'
  have hfm : Fused a (a * a') := caseA_fused_mul hCa hfa haa'.symm hne
  have hbQ : a * a' ∈ coreAt z := Subgroup.mul_mem _ haQ ha'Q
  have haa : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by
      rw [← hCa.orderOf_eq]
      exact pow_orderOf_eq_one a
    rwa [sq] at h2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  refine ⟨ha.trans hfm, hbQ, ?_⟩
  intro hz
  apply hnez
  calc a' = a⁻¹ * (a * a') := by group
    _ = a⁻¹ * z := by rw [hz]
    _ = a * z := by rw [hainv]

theorem CaseA.eq_or_eq_mul_of_commute (hC : Config z n) (hA : CaseA z) {a x a' : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a)
    (ha' : Fused z a') (ha'Q : a' ∈ coreAt z) (ha'z : a' ≠ z) (haa' : a * a' = a' * a) :
    a' = a ∨ a' = a * z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hnez⟩ := hcon
  obtain ⟨hfb, hbQ, hbz⟩ := CaseA.mul_mem hC hA ha haQ haz ha' ha'Q haa' hne hnez
  have hab : a * (a * a') = a * a' * a := by
    calc a * (a * a') = a * (a' * a) := by rw [haa']
      _ = a * a' * a := by group
  have hxa'nc : a' * x ≠ x * a' := by
    intro h
    exact hax (CaseA.commute_of_commute hC hA ha' ha'Q ha'z ha haQ hx hxQ haa'.symm h)
  have hxa' : ⁅x, a'⁆ = z := by
    refine (hC.comm_eq x hxQ a' ha'Q).resolve_left ?_
    intro h
    exact hxa'nc (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  have hxa : ⁅x, a⁆ = z := by
    refine (hC.comm_eq x hxQ a haQ).resolve_left ?_
    intro h
    exact hax (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  have hzz : z * z = 1 := by
    have h2 : z ^ 2 = 1 := by
      rw [← hC.orderOf_eq]
      exact pow_orderOf_eq_one z
    rwa [sq] at h2
  have hxb : ⁅x, a * a'⁆ = 1 := by
    rw [hC.commutator_mul hxQ haQ ha'Q, hxa, hxa', hzz]
  have hxb' : x * (a * a') = a * a' * x := commutatorElement_eq_one_iff_mul_comm.1 hxb
  have hcon2 : x * a = a * x :=
    CaseA.commute_of_commute hC hA hfb hbQ hbz hx hxQ ha haQ hxb'.symm hab.symm
  exact hax hcon2.symm

end CFSG.GF2Type.CenterFour
