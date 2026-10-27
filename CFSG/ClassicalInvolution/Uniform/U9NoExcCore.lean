module

public import CFSG.ClassicalInvolution.Uniform.U8Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3)
open scoped MatrixGroups commutatorElement



section Subnormal

variable {X : Type*} [Group X]

theorem isSubnormal_map_conj_of_mem {A B : Subgroup X} (h : CFSG.Open.IsSubnormal A B) {y : X}
    (hy : y ∈ B) : CFSG.Open.IsSubnormal (A.map (MulAut.conj y).toMonoidHom) B := by
  induction h with
  | refl H =>
    have : H.map (MulAut.conj y).toMonoidHom = H := conjSub_eq_self_of_mem hy
    rw [this]
    exact CFSG.Open.IsSubnormal.refl H
  | @step H M K' hHM hHN hMK ih =>
    refine CFSG.Open.IsSubnormal.step (Subgroup.map_mono hHM) ?_ (ih hy)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨a, ha, hna⟩ := hn
    obtain ⟨m, hm, hgm⟩ := g.2
    have h1 := hHN.conj_mem ⟨a, hHM ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨m, hm⟩
    have h1' : m * a * m⁻¹ ∈ H := Subgroup.mem_subgroupOf.1 h1
    refine ⟨m * a * m⁻¹, h1', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hna hgm ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, ← hna, ← hgm]
    group

end Subnormal

section Reduction

variable {K G : Type} [Group K] [Finite K] [Group G]

theorem twinRatio_notMem_center_of_normalizes (θ : K →* G)
    (hker : θ.ker ≤ Subgroup.center K) (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1)
    (hcen : ∀ c ∈ Subgroup.center K, θ c = 1) {Fund : Set (Subgroup K)}
    (hsingle : ∀ R ∈ Fund, ∀ R' ∈ Fund, ∃ g : K, R' = conjSub g R)
    (hgen : ∀ R ∈ Fund, Gen3 R) {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {R₀ : Subgroup K} (hR₀ : R₀ ∈ Fund) (e₀ : R₀ ≃* SL(2, F))
    (hnorm : ∀ g : K, θ g * θ (sl2Inv e₀) = θ (sl2Inv e₀) * θ g →
      (conjSub g R₀).map θ = R₀.map θ)
    {R₁ R₂ : Subgroup K} (h₁ : R₁ ∈ Fund) (h₂ : R₂ ∈ Fund) (hne : R₁ ≠ R₂)
    (e₁ : R₁ ≃* SL(2, F)) (e₂ : R₂ ≃* SL(2, F)) :
    sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∉ Subgroup.center K := by
  intro hc
  obtain ⟨g₁, hg₁⟩ := hsingle R₀ hR₀ R₁ h₁
  obtain ⟨g₂, hg₂⟩ := hsingle R₀ hR₀ R₂ h₂
  have hinv : ∀ (g : K) (R : Subgroup K) (e : R ≃* SL(2, F)), R = conjSub g R₀ →
      sl2Inv e = g * sl2Inv e₀ * g⁻¹ := by
    intro g R e hR
    refine (eq_sl2Inv_of_orderOf_eq_two hodd e ?_ ?_).symm
    · rw [hR]
      exact conj_mem_conjSub (sl2Inv_mem e₀)
    · have h := MulEquiv.orderOf_eq (MulAut.conj g) (sl2Inv e₀)
      simp only [MulAut.conj_apply] at h
      rw [h]
      exact orderOf_sl2Inv hodd e₀
  have hi₁ := hinv g₁ R₁ e₁ hg₁
  have hi₂ := hinv g₂ R₂ e₂ hg₂
  have hθ1 := hcen _ hc
  rw [map_mul, map_inv, mul_inv_eq_one, hi₁, hi₂] at hθ1
  simp only [map_mul, map_inv] at hθ1
  have hcomm : θ (g₁⁻¹ * g₂) * θ (sl2Inv e₀) = θ (sl2Inv e₀) * θ (g₁⁻¹ * g₂) := by
    simp only [map_mul, map_inv]
    calc (θ g₁)⁻¹ * θ g₂ * θ (sl2Inv e₀)
        = (θ g₁)⁻¹ * (θ g₂ * θ (sl2Inv e₀) * (θ g₂)⁻¹) * θ g₂ := by group
      _ = (θ g₁)⁻¹ * (θ g₁ * θ (sl2Inv e₀) * (θ g₁)⁻¹) * θ g₂ := by rw [hθ1]
      _ = θ (sl2Inv e₀) * ((θ g₁)⁻¹ * θ g₂) := by group
  have hgenA : Gen3 (conjSub (g₁⁻¹ * g₂) R₀) :=
    (hgen R₀ hR₀).map (MulAut.conj (g₁⁻¹ * g₂)).toMonoidHom
  have hEq : conjSub (g₁⁻¹ * g₂) R₀ = R₀ :=
    eq_of_map_eq_of_gen3 θ hker hk3 hgenA (hgen R₀ hR₀) (hnorm _ hcomm)
  apply hne
  rw [hg₁, hg₂]
  calc conjSub g₁ R₀ = conjSub g₁ (conjSub (g₁⁻¹ * g₂) R₀) := by rw [hEq]
    _ = conjSub g₂ R₀ := by rw [← conjSub_mul]; congr 1; group

end Reduction

end CFSG.ClassicalInvolution.Uniform
