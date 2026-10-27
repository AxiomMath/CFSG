module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphTwist

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Abstract

variable {G : Type*} [Group G]

@[expose] def relayConjRestrict (E : Subgroup G) (t : G) (ht : ∀ a ∈ E, t * a * t⁻¹ ∈ E)
    (ht' : ∀ a ∈ E, t⁻¹ * a * t ∈ E) : MulAut E where
  toFun a := ⟨t * a * t⁻¹, ht a a.2⟩
  invFun a := ⟨t⁻¹ * a * t, ht' a a.2⟩
  left_inv a := Subtype.ext (by
    change t⁻¹ * (t * (a : G) * t⁻¹) * t = a
    group)
  right_inv a := Subtype.ext (by
    change t * (t⁻¹ * (a : G) * t) * t⁻¹ = a
    group)
  map_mul' a b := Subtype.ext (by
    change t * ((a : G) * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
    group)

theorem coe_relayConjRestrict (E : Subgroup G) (t : G) (ht : ∀ a ∈ E, t * a * t⁻¹ ∈ E)
    (ht' : ∀ a ∈ E, t⁻¹ * a * t ∈ E) (a : E) :
    ((relayConjRestrict E t ht ht' a : E) : G) = t * a * t⁻¹ :=
  rfl

theorem eq_or_eq_conj_of_agree {E S : Subgroup G} (hSE : S ≤ E)
    (hC : ∀ a ∈ E, (∀ s ∈ S, a * s = s * a) → a = 1)
    (hOut : ∀ α β : MulAut E, α ∉ (MulAut.conj : E →* MulAut E).range →
      β ∉ (MulAut.conj : E →* MulAut E).range →
        α * β⁻¹ ∈ (MulAut.conj : E →* MulAut E).range)
    {t : G} (ht : ∀ a ∈ E, t * a * t⁻¹ ∈ E) (ht' : ∀ a ∈ E, t⁻¹ * a * t ∈ E)
    (htS : ∀ s ∈ S, t * s * t⁻¹ = s) (htm : ∃ a ∈ E, t * a * t⁻¹ ≠ a)
    {H : Type*} [Group H] [Finite H] {α α' : H →* G} (hα : Function.Injective α)
    (hα' : Function.Injective α') (hr : α.range = E) (hr' : α'.range ≤ E)
    (hS : ∀ x, α x ∈ S → α' x = α x) :
    (∀ x, α' x = α x) ∨ ∀ x, α' x = t * α x * t⁻¹ := by
  have hfin : Finite E := by
    rw [← hr]
    exact Finite.of_equiv H (MonoidHom.ofInjective hα).toEquiv
  have hcard : Nat.card α'.range = Nat.card E := by
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hα).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hα').toEquiv]
  have hr'' : α'.range = E := Subgroup.eq_of_le_of_card_ge hr' hcard.ge
  set iα : H ≃* E := (MonoidHom.ofInjective hα).trans (MulEquiv.subgroupCongr hr) with hiα
  set iα' : H ≃* E := (MonoidHom.ofInjective hα').trans (MulEquiv.subgroupCongr hr'')
    with hiα'
  have hiαc : ∀ x, ((iα x : E) : G) = α x := fun x => rfl
  have hiαc' : ∀ x, ((iα' x : E) : G) = α' x := fun x => rfl
  set θ : MulAut E := iα.symm.trans iα' with hθ
  have hθa : ∀ x, θ (iα x) = iα' x := fun x => by
    rw [hθ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set γ : MulAut E := relayConjRestrict E t ht ht' with hγdef
  set S' : Subgroup E := S.subgroupOf E with hS'
  have hC' : ∀ a : E, (∀ s ∈ S', a * s = s * a) → a = 1 := by
    intro a ha
    apply Subtype.ext
    refine hC a a.2 fun s hs => ?_
    have h := congrArg Subtype.val (ha ⟨s, hSE hs⟩ (by rw [hS', mem_subgroupOf]; exact hs))
    exact h
  have hγ : ∀ s ∈ S', γ s = s := by
    intro s hs
    apply Subtype.ext
    rw [hγdef, coe_relayConjRestrict]
    exact htS s (by rw [hS', mem_subgroupOf] at hs; exact hs)
  have hγo : γ ∉ (MulAut.conj : E →* MulAut E).range := by
    rintro ⟨a, ha⟩
    have ha1 : a = 1 := hC' a fun s hs => by
      have h := hγ s hs
      rw [← ha, MulAut.conj_apply] at h
      calc a * s = a * s * a⁻¹ * a := by group
        _ = s * a := by rw [h]
    rw [ha1, map_one] at ha
    obtain ⟨b, hb, hne⟩ := htm
    apply hne
    have h := congrArg (fun φ : MulAut E => ((φ ⟨b, hb⟩ : E) : G)) ha
    simpa [hγdef, coe_relayConjRestrict] using h.symm
  have hτ : ∀ s ∈ S', θ s = s := by
    intro s hs
    rw [hS', mem_subgroupOf] at hs
    obtain ⟨x, rfl⟩ := iα.surjective s
    rw [hθa]
    apply Subtype.ext
    rw [hiαc, hiαc']
    exact hS x (by rw [← hiαc]; exact hs)
  rcases SymplecticPilot.eq_one_or_eq_of_fix hC' hOut hγ hγo hτ with h | h
  · left
    intro x
    rw [← hiαc', ← hθa, h, MulAut.one_apply, hiαc]
  · right
    intro x
    rw [← hiαc', ← hθa, h, hγdef, coe_relayConjRestrict, hiαc]

theorem eq_or_eq_conj_of_agree_projectiveSL {K : Type} [Field K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 3 ≤ n) {E S : Subgroup G} (χ : E ≃* LinearFlag.projectiveSL n K) (hSE : S ≤ E)
    (hC : ∀ a ∈ E, (∀ s ∈ S, a * s = s * a) → a = 1)
    {t : G} (ht : ∀ a ∈ E, t * a * t⁻¹ ∈ E) (ht' : ∀ a ∈ E, t⁻¹ * a * t ∈ E)
    (htS : ∀ s ∈ S, t * s * t⁻¹ = s) (htm : ∃ a ∈ E, t * a * t⁻¹ ≠ a)
    {H : Type*} [Group H] [Finite H] {α α' : H →* G} (hα : Function.Injective α)
    (hα' : Function.Injective α') (hr : α.range = E) (hr' : α'.range ≤ E)
    (hS : ∀ x, α x ∈ S → α' x = α x) :
    (∀ x, α' x = α x) ∨ ∀ x, α' x = t * α x * t⁻¹ :=
  eq_or_eq_conj_of_agree hSE hC
    (fun _ _ ha hb => SymplecticPilot.mul_inv_mem_inner_of_not_mem hK hn χ ha hb) ht ht' htS htm
    hα hα' hr hr' hS

theorem commute_of_eq_or_eq_conj {H : Type*} [Group H] {α α' : H →* G} {t v : G}
    (h : (∀ x, α' x = α x) ∨ ∀ x, α' x = t * α x * t⁻¹) (hvt : Commute v t) {x : H}
    (hv : Commute v (α' x)) : Commute v (α x) := by
  rcases h with h | h
  · rwa [h x] at hv
  · rw [h x] at hv
    have e : α x = t⁻¹ * (t * α x * t⁻¹) * t := by group
    rw [e]
    exact (hvt.inv_right.mul_right hv).mul_right hvt

end Abstract

end CFSG.SeitzReduction.F4Pilot
