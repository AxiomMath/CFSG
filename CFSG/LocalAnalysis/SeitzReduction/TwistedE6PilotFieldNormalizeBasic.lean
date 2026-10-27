module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Normalize

variable {A M E : Type*} [Group A] [Group M] [Group E]

theorem fixedSubgroup_mulAutCongr (ψ : M ≃* E) (β : MulAut M) :
    fixedSubgroup (MulAut.congr ψ β) = (fixedSubgroup β).map ψ.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨ψ.symm x, ?_, by simp⟩
    have hx' : ψ (β (ψ.symm x)) = x := hx
    change β (ψ.symm x) = ψ.symm x
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hx'
  · rintro ⟨y, hy, rfl⟩
    have hy' : β y = y := hy
    change ψ (β (ψ.symm (ψ y))) = ψ y
    rw [MulEquiv.symm_apply_apply, hy']

theorem exists_normalized_mulEquiv [Finite M] [Finite E] {j : A →* M} (hj : Function.Injective j)
    {β₀ : MulAut M}
    (hj₀ : j.range = perfectCore (fixedSubgroup β₀))
    (hdesc : ∀ β : MulAut M, β * β = 1 → Nonempty (perfectCore (fixedSubgroup β) ≃* A) →
      ∃ ψ : MulAut M, ψ * β * ψ⁻¹ = β₀)
    (hext : ∀ δ : MulAut A, ∃ δ' : MulAut M, (∀ a, δ' (j a) = j (δ a)) ∧ δ' * β₀ = β₀ * δ')
    (ψ₀ : M ≃* E) {θ : MulAut E} (hθ : θ * θ = 1) {ε : A →* E} (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (fixedSubgroup θ)) :
    ∃ Φ : M ≃* E, (∀ a, Φ (j a) = ε a) ∧ ∀ x, Φ (β₀ x) = θ (Φ x) := by
  set β : MulAut M := MulAut.congr ψ₀.symm θ with hβdef
  have hββ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  have hβfix : fixedSubgroup β = (fixedSubgroup θ).map ψ₀.symm.toMonoidHom :=
    fixedSubgroup_mulAutCongr ψ₀.symm θ
  have hβcore : perfectCore (fixedSubgroup β) = ε.range.map ψ₀.symm.toMonoidHom := by
    rw [hβfix, ← CFSG.Quasithin.map_perfectCore, hεr]
  have hiso : Nonempty (perfectCore (fixedSubgroup β) ≃* A) :=
    ⟨(MulEquiv.subgroupCongr hβcore).trans ((ε.range.equivMapOfInjective _
      ψ₀.symm.injective).symm.trans ((MonoidHom.ofInjective hε).symm))⟩
  obtain ⟨ψ, hψ⟩ := hdesc β hββ hiso
  set Φ₁ : M ≃* E := ψ.symm.trans ψ₀ with hΦ₁def
  have hΦ₁β : ∀ x, Φ₁ (β₀ x) = θ (Φ₁ x) := by
    intro x
    have h1 : β₀ x = ψ (β (ψ⁻¹ x)) := by
      rw [← hψ]
      rfl
    rw [hΦ₁def, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    change ψ₀ (ψ.symm (ψ (β (ψ.symm x)))) = θ (ψ₀ (ψ.symm x))
    rw [MulEquiv.symm_apply_apply, hβdef]
    change ψ₀ (ψ₀.symm (θ (ψ₀ (ψ.symm x)))) = θ (ψ₀ (ψ.symm x))
    rw [MulEquiv.apply_symm_apply]
  have hfixΦ : fixedSubgroup θ = (fixedSubgroup β₀).map Φ₁.toMonoidHom := by
    have hc : MulAut.congr Φ₁ β₀ = θ := MulEquiv.ext fun y => by
      change Φ₁ (β₀ (Φ₁.symm y)) = θ y
      rw [hΦ₁β, MulEquiv.apply_symm_apply]
    rw [← hc, fixedSubgroup_mulAutCongr]
  have hrange : (Φ₁.symm.toMonoidHom.comp ε).range = j.range := by
    rw [MonoidHom.range_comp, hεr, hfixΦ, ← CFSG.Quasithin.map_perfectCore, Subgroup.map_map,
      hj₀]
    have hid : Φ₁.symm.toMonoidHom.comp Φ₁.toMonoidHom = MonoidHom.id M :=
      MonoidHom.ext fun x => Φ₁.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  have hinj : Function.Injective (Φ₁.symm.toMonoidHom.comp ε) := Φ₁.symm.injective.comp hε
  set δ : MulAut A := ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (MonoidHom.ofInjective hj).symm with hδdef
  have hδ : ∀ a, j (δ a) = Φ₁.symm (ε a) := by
    intro a
    have h1 := (MonoidHom.ofInjective hj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj a))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδβ⟩ := hext δ
  refine ⟨δ'.trans Φ₁, fun a => ?_, fun x => ?_⟩
  · rw [MulEquiv.trans_apply, hδ', hδ, MulEquiv.apply_symm_apply]
  · have h1 : δ' (β₀ x) = β₀ (δ' x) := by
      have := congrArg (fun α : MulAut M => α x) hδβ
      exact this
    show Φ₁ (δ' (β₀ x)) = θ (Φ₁ (δ' x))
    rw [h1, hΦ₁β]

@[expose] def InvolutionDescent (β₀ : MulAut M) (A : Type*) [Group A] : Prop :=
  ∀ β : MulAut M, β * β = 1 → Nonempty (perfectCore (fixedSubgroup β) ≃* A) →
    ∃ ψ : MulAut M, ψ * β * ψ⁻¹ = β₀

@[expose] def AutExtensionComm (j : A →* M) (β₀ : MulAut M) : Prop :=
  ∀ δ : MulAut A, ∃ δ' : MulAut M, (∀ a, δ' (j a) = j (δ a)) ∧ δ' * β₀ = β₀ * δ'

@[expose] def FixRigid (j : A →* M) (β₀ : MulAut M) : Prop :=
  ∀ α : MulAut M, (∀ a, α (j a) = j a) → α = 1 ∨ α = β₀

@[expose] def InvolutionDescentComp (β₀ : MulAut M) (A : Type*) [Group A] : Prop :=
  ∀ β : MulAut M, β * β = 1 →
    (∃ C : Subgroup (fixedSubgroup β), CFSG.IsComponent C ∧ Nonempty (C ≃* A)) →
      ∃ ψ : MulAut M, ψ * β * ψ⁻¹ = β₀

theorem exists_normalized_mulEquiv_of_fix_eq [Finite A] {j : A →* M} (hj : Function.Injective j)
    {β₀ : MulAut M} (hj₀ : j.range = fixedSubgroup β₀) (hdesc : InvolutionDescentComp β₀ A)
    (hext : AutExtensionComm j β₀) (ψ₀ : M ≃* E) {θ : MulAut E} (hθ : θ * θ = 1) {ε : A →* E}
    (hε : Function.Injective ε) (hεθ : ε.range ≤ fixedSubgroup θ)
    (hεC : CFSG.IsComponent (ε.range.subgroupOf (fixedSubgroup θ))) :
    ∃ Φ : M ≃* E, (∀ a, Φ (j a) = ε a) ∧ ∀ x, Φ (β₀ x) = θ (Φ x) := by
  set β : MulAut M := MulAut.congr ψ₀.symm θ with hβdef
  have hββ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  have hβfix : fixedSubgroup β = (fixedSubgroup θ).map ψ₀.symm.toMonoidHom :=
    fixedSubgroup_mulAutCongr ψ₀.symm θ
  set eFix : fixedSubgroup θ ≃* fixedSubgroup β :=
    ((fixedSubgroup θ).equivMapOfInjective _ ψ₀.symm.injective).trans
      (MulEquiv.subgroupCongr hβfix.symm) with heFix
  have hcomp : ∃ C : Subgroup (fixedSubgroup β), CFSG.IsComponent C ∧ Nonempty (C ≃* A) :=
    ⟨(ε.range.subgroupOf (fixedSubgroup θ)).map eFix.toMonoidHom,
      CFSG.LocalCores.isComponent_map_mulEquiv eFix hεC,
      ⟨(((ε.range.subgroupOf (fixedSubgroup θ)).equivMapOfInjective _ eFix.injective).symm.trans
        (subgroupOfEquivOfLe hεθ)).trans (MonoidHom.ofInjective hε).symm⟩⟩
  obtain ⟨ψ, hψ⟩ := hdesc β hββ hcomp
  set Φ₁ : M ≃* E := ψ.symm.trans ψ₀ with hΦ₁def
  have hΦ₁β : ∀ x, Φ₁ (β₀ x) = θ (Φ₁ x) := by
    intro x
    have h1 : β₀ x = ψ (β (ψ⁻¹ x)) := by
      rw [← hψ]
      rfl
    rw [hΦ₁def, MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    change ψ₀ (ψ.symm (ψ (β (ψ.symm x)))) = θ (ψ₀ (ψ.symm x))
    rw [MulEquiv.symm_apply_apply, hβdef]
    change ψ₀ (ψ₀.symm (θ (ψ₀ (ψ.symm x)))) = θ (ψ₀ (ψ.symm x))
    rw [MulEquiv.apply_symm_apply]
  have hfixΦ : fixedSubgroup θ = (fixedSubgroup β₀).map Φ₁.toMonoidHom := by
    have hc : MulAut.congr Φ₁ β₀ = θ := MulEquiv.ext fun y => by
      change Φ₁ (β₀ (Φ₁.symm y)) = θ y
      rw [hΦ₁β, MulEquiv.apply_symm_apply]
    rw [← hc, fixedSubgroup_mulAutCongr]
  have hfinA : Finite (j.range.map Φ₁.toMonoidHom) := by
    have hc : Nat.card (j.range.map Φ₁.toMonoidHom) = Nat.card A := by
      rw [card_map_of_injective Φ₁.injective]
      exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
    exact Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  have hεeq : ε.range = j.range.map Φ₁.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge (hεθ.trans (by rw [hfixΦ, hj₀])) ?_
    rw [card_map_of_injective Φ₁.injective, ← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hε).toEquiv]
  have hrange : (Φ₁.symm.toMonoidHom.comp ε).range = j.range := by
    rw [MonoidHom.range_comp, hεeq, Subgroup.map_map]
    have hid : Φ₁.symm.toMonoidHom.comp Φ₁.toMonoidHom = MonoidHom.id M :=
      MonoidHom.ext fun x => Φ₁.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  have hinj : Function.Injective (Φ₁.symm.toMonoidHom.comp ε) := Φ₁.symm.injective.comp hε
  set δ : MulAut A := ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (MonoidHom.ofInjective hj).symm with hδdef
  have hδ : ∀ a, j (δ a) = Φ₁.symm (ε a) := by
    intro a
    have h1 := (MonoidHom.ofInjective hj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hinj a))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδβ⟩ := hext δ
  refine ⟨δ'.trans Φ₁, fun a => ?_, fun x => ?_⟩
  · rw [MulEquiv.trans_apply, hδ', hδ, MulEquiv.apply_symm_apply]
  · have h1 : δ' (β₀ x) = β₀ (δ' x) := congrArg (fun α : MulAut M => α x) hδβ
    show Φ₁ (δ' (β₀ x)) = θ (Φ₁ (δ' x))
    rw [h1, hΦ₁β]

end Normalize

end CFSG.SeitzReduction.TwistedE6Pilot
