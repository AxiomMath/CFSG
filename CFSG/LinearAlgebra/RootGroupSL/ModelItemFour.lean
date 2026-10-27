module

public import CFSG.LinearAlgebra.RootGroupSL.ModelAutP
public import CFSG.LinearAlgebra.RootGroupSL.ModelGenerateU
public import CFSG.LinearAlgebra.RootGroupSL.DetCoprime

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma transport_mulAut {G : Type*} [Group G] {H H' : Subgroup G} (h : H = H')
    (α : MulAut ↥H) :
    ∃ α' : MulAut ↥H', ∀ (x : G) (hx : x ∈ H) (hx' : x ∈ H'),
      ((α' ⟨x, hx'⟩ : ↥H') : G) = ((α ⟨x, hx⟩ : ↥H) : G) := by
  refine ⟨(MulEquiv.subgroupCongr h).symm.trans (α.trans (MulEquiv.subgroupCongr h)), ?_⟩
  intro x hx hx'
  have hfix : (MulEquiv.subgroupCongr h).symm ⟨x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext rfl
  simp only [MulEquiv.trans_apply]
  rw [hfix]
  simp

private lemma smulOfUnit_mul_comm {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (μ : kˣ) (y : V ≃ₗ[k] V) :
    LinearEquiv.smulOfUnit μ * y = y * LinearEquiv.smulOfUnit μ := by
  apply LinearEquiv.ext
  intro v
  change (μ : k) • y v = y ((μ : k) • v)
  rw [map_smul]

private lemma smulOfUnit_conj {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (μ : kˣ) (y : V ≃ₗ[k] V) :
    LinearEquiv.smulOfUnit μ * y * (LinearEquiv.smulOfUnit μ)⁻¹ = y := by
  rw [smulOfUnit_mul_comm μ y, mul_assoc, mul_inv_cancel, mul_one]

private lemma exists_conj_of_sup_eq_modelP
    {U P : Subgroup (SpecialLinearGroup k (VJ × V₀))}
    (hUP : modelJ k E VJ V₀ ⊔ U = P)
    (hcop : Nat.Coprime (Module.finrank k (VJ × V₀)) (Nat.card k - 1))
    (hconj : ∀ (β : MulAut ↥P),
      (∀ j : ↥P, (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → β j = j) →
      ∃ z : (VJ × V₀) ≃ₗ[k] (VJ × V₀), ∀ p : ↥P,
        SpecialLinearGroup.toLinearEquiv ((β p : ↥P) : SpecialLinearGroup k (VJ × V₀)) =
          z * SpecialLinearGroup.toLinearEquiv (p : SpecialLinearGroup k (VJ × V₀)) * z⁻¹)
    (α : MulAut ↥(modelJ k E VJ V₀ ⊔ U))
    (hα : ∀ j : ↥(modelJ k E VJ V₀ ⊔ U),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α j = j) :
    ∃ h : SpecialLinearGroup k (VJ × V₀), ∀ x : ↥(modelJ k E VJ V₀ ⊔ U),
      ((α x : ↥(modelJ k E VJ V₀ ⊔ U)) : SpecialLinearGroup k (VJ × V₀)) =
        h * (x : SpecialLinearGroup k (VJ × V₀)) * h⁻¹ := by
  haveI : Module.Finite k (VJ × V₀) := Module.Finite.prod
  obtain ⟨α', hα'⟩ := transport_mulAut hUP α
  have hα'J : ∀ j : ↥P,
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α' j = j := by
    intro j hj
    have hjU : (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ ⊔ U := hUP ▸ j.prop
    have h := hα' (j : SpecialLinearGroup k (VJ × V₀)) hjU j.prop
    have hfix := hα ⟨(j : SpecialLinearGroup k (VJ × V₀)), hjU⟩ hj
    rw [hfix] at h
    exact Subtype.ext h
  obtain ⟨z, hz⟩ := hconj α' hα'J
  obtain ⟨h, μ, hμ, hh⟩ := exists_specialLinear_smul_eq hcop z
  refine ⟨h, ?_⟩
  intro x
  apply SpecialLinearGroup.toLinearEquiv_injective
  have hxP : (x : SpecialLinearGroup k (VJ × V₀)) ∈ P := hUP ▸ x.prop
  let p : ↥P := ⟨(x : SpecialLinearGroup k (VJ × V₀)), hxP⟩
  have htransfer : ((α x : ↥(modelJ k E VJ V₀ ⊔ U)) : SpecialLinearGroup k (VJ × V₀)) =
      ((α' p : ↥P) : SpecialLinearGroup k (VJ × V₀)) :=
    (hα' (x : SpecialLinearGroup k (VJ × V₀)) x.prop hxP).symm
  have hp : (p : SpecialLinearGroup k (VJ × V₀)) =
      (x : SpecialLinearGroup k (VJ × V₀)) := rfl
  have hz' : SpecialLinearGroup.toLinearEquiv
      (((α x : ↥(modelJ k E VJ V₀ ⊔ U)) : SpecialLinearGroup k (VJ × V₀))) =
      z * SpecialLinearGroup.toLinearEquiv (x : SpecialLinearGroup k (VJ × V₀)) * z⁻¹ := by
    rw [htransfer]
    simpa only [hp] using hz p
  rw [hz']
  rw [map_mul, map_mul, map_inv]
  let s : (VJ × V₀) ≃ₗ[k] (VJ × V₀) := LinearEquiv.smulOfUnit (Units.mk0 μ hμ)
  have hlin : SpecialLinearGroup.toLinearEquiv h = s * z := by
    apply LinearEquiv.ext
    intro v
    change h v = s (z v)
    rw [hh v]
    rfl
  rw [hlin]
  rw [mul_inv_rev]
  have hgrp : (s * z) * SpecialLinearGroup.toLinearEquiv (x : SpecialLinearGroup k (VJ × V₀)) *
      (z⁻¹ * s⁻¹) =
      s * (z * SpecialLinearGroup.toLinearEquiv (x : SpecialLinearGroup k (VJ × V₀)) * z⁻¹) *
        s⁻¹ := by
    group
  rw [hgrp]
  exact (smulOfUnit_conj (Units.mk0 μ hμ)
    (z * SpecialLinearGroup.toLinearEquiv (x : SpecialLinearGroup k (VJ × V₀)) * z⁻¹)).symm

theorem exists_conj_of_mulAut_sup (hm : 3 ≤ Module.finrank E VJ) (hc : 2 ≤ Module.finrank k E)
    (hcop : Nat.Coprime (Module.finrank k (VJ × V₀)) (Nat.card k - 1)) {e₀ : VJ}
    {l₀ : VJ →ₗ[E] E} (U : Subgroup (SpecialLinearGroup k (VJ × V₀)))
    (hU : (e₀ ≠ 0 ∧ U = datumU1 (modelIota (E := E) k V₀ e₀)) ∨
      (l₀ ≠ 0 ∧ U = datumU2 (modelPi k V₀ l₀)))
    (α : MulAut ↥(modelJ k E VJ V₀ ⊔ U))
    (hα : ∀ j : ↥(modelJ k E VJ V₀ ⊔ U),
      (j : SpecialLinearGroup k (VJ × V₀)) ∈ modelJ k E VJ V₀ → α j = j) :
    ∃ h : SpecialLinearGroup k (VJ × V₀), ∀ x : ↥(modelJ k E VJ V₀ ⊔ U),
      ((α x : ↥(modelJ k E VJ V₀ ⊔ U)) : SpecialLinearGroup k (VJ × V₀)) =
        h * (x : SpecialLinearGroup k (VJ × V₀)) * h⁻¹ := by
  rcases hU with ⟨he, hU⟩ | ⟨hl, hU⟩
  · subst U
    exact exists_conj_of_sup_eq_modelP (hUP := modelJ_sup_datumU1 hm he) hcop
      (fun β hβ => exists_conj_of_mulAut_modelP1 hm hc β hβ) α hα
  · subst U
    exact exists_conj_of_sup_eq_modelP (hUP := modelJ_sup_datumU2 hm hl) hcop
      (fun β hβ => exists_conj_of_mulAut_modelP2 hm hc β hβ) α hα

end CFSG.LinearAlgebra.RootGroupSL
