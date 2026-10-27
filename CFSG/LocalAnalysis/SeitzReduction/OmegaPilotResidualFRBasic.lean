module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixFR

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Outer

@[expose] def OuterCommutative (X : Type*) [Group X] : Prop :=
  ∀ μ θ : MulAut X, μ * θ * μ⁻¹ * θ⁻¹ ∈ inner X

theorem outerCommutative_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterCommutative Y) : OuterCommutative X := by
  intro μ θ
  obtain ⟨y, hy⟩ := h (MulAut.congr e μ) (MulAut.congr e θ)
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  have hc : MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [hc, hy, map_mul, map_mul, map_mul, map_inv, map_inv]

open CFSG.Assembly.LowTwoRank (StatedProj StatedSp) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem outerCommutative_statedProj_statedSp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hr : 3 ≤ r) : OuterCommutative (StatedProj (StatedSp r K)) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hr
  obtain ⟨-, -, hDn, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  have hDnorm : (spLinearAutGroup r K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  have hDle : spLinearAutGroup r K ≤ inner (StatedProj (StatedSp r K)) := by
    intro δ hδ
    obtain ⟨A, rfl⟩ := (mem_spLinearAutGroup_iff).mp hδ
    exact conjAut_mem_inner_of_isSquare
      (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplier r K A : K))
  have hgE : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ k : ℤ,
      g ^ k * α ∈ spLinearAutGroup r K := fun α => hg α (hgenTop ▸ Subgroup.mem_top α)
  intro μ θ
  have h := CFSG.RankThree.PartOne.OutStructure.commutator_mem_of_cyclic_quotient g hgE μ θ
  rw [commutatorElement_def] at h
  exact hDle h

end Outer

section Rigid

variable {C : Type*} [Group C] {L : Type*} [Field L] [Finite L]

theorem fieldRigidInOf_map (fp : MulAut C →* (L ≃+* L)) {X₁ X₂ : Subgroup C}
    (h : FieldRigidInOf fp X₁ X₂) (δ₁ δ₂ : MulAut C) :
    FieldRigidInOf fp (X₁.map δ₁.toMonoidHom) (X₂.map δ₂.toMonoidHom) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁ hc₁ hc₂
  have hcls : ∀ (δ β : MulAut C), fp (δ⁻¹ * β * δ) = fp β := fun δ β => by
    rw [map_mul, map_mul, map_inv, LinearPilot.ringEquiv_mul_comm (fp δ)⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  have hX' : X₁.map (φ₁.comp δ₁.toMonoidHom) = X₂.map (φ₂.comp δ₂.toMonoidHom) := by
    rw [← Subgroup.map_map, ← Subgroup.map_map, hX]
  have key := h Γ (φ₁.comp δ₁.toMonoidHom) (φ₂.comp δ₂.toMonoidHom)
    (hφ₁.comp δ₁.injective) (hφ₂.comp δ₂.injective) hX' γ (δ₁⁻¹ * β₁ * δ₁) (δ₂⁻¹ * β₂ * δ₂)
    (fun x hx => by
      have hx' : δ₁ x ∈ X₁.map δ₁.toMonoidHom := ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hβ₁ _ hx'
      have : (δ₁⁻¹ * β₁ * δ₁) x = y := by
        rw [MulAut.mul_apply, MulAut.mul_apply, ← hyx]
        exact δ₁.symm_apply_apply y
      rw [this]
      exact hy)
    (fun x => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.mul_apply]
      rw [← hc₁ (δ₁ x)]
      congr 1
      exact δ₁.apply_symm_apply _)
    (fun x => by
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.mul_apply]
      rw [← hc₂ (δ₂ x)]
      congr 1
      exact δ₂.apply_symm_apply _)
  rwa [hcls, hcls] at key

omit [Finite L] in
theorem fieldRigidInOf_self_of_centralizer [Finite C] (fp : MulAut C →* (L ≃+* L))
    {X : Subgroup C} (hinn : ∀ x : C, fp (MulAut.conj x) = 1)
    (hcen : ∀ β : MulAut C, (∀ x ∈ X, β x = x) → fp β = 1) (hout : OuterCommutative X) :
    FieldRigidInOf fp X X := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβ₁ hc₁ hc₂
  set ψ : ↥X ≃* ↥X := (X.equivMapOfInjective φ₁ hφ₁).trans
    ((MulEquiv.subgroupCongr hX).trans (X.equivMapOfInjective φ₂ hφ₂).symm) with hψ
  have hψφ : ∀ x : X, φ₂ (ψ x : C) = φ₁ x := fun x => by
    have h1 : X.equivMapOfInjective φ₂ hφ₂ (ψ x) =
        MulEquiv.subgroupCongr hX (X.equivMapOfInjective φ₁ hφ₁ x) := by
      rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun y : ↥(X.map φ₂) => (y : Γ)) h1
    simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  have hkey : ∀ x : X, β₂ (ψ x : C) = (ψ ⟨β₁ x, hβ₁ x x.2⟩ : C) := fun x => by
    apply hφ₂
    rw [hc₂, hψφ, hψφ, hc₁]
  have hβ₂ : ∀ y ∈ X, β₂ y ∈ X := fun y hy => by
    obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
    have : y = (ψ x : C) := by rw [hx]
    rw [this, hkey]
    exact (ψ _).2
  set θ₁ := restrictAutOfMapsTo β₁ X hβ₁ with hθ₁
  set θ₂ := restrictAutOfMapsTo β₂ X hβ₂ with hθ₂
  have hconj : θ₂ * ψ = ψ * θ₁ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [MulAut.mul_apply, MulAut.mul_apply, coe_restrictAutOfMapsTo, hkey]
    rfl
  have hθ : θ₂ = ψ * θ₁ * ψ⁻¹ := by rw [← hconj, mul_inv_cancel_right]
  obtain ⟨x₀, hx₀⟩ := hout ψ θ₁
  have hθ' : θ₂ = MulAut.conj x₀ * θ₁ := by
    rw [hx₀, hθ, inv_mul_cancel_right]
  have hfix : ∀ y ∈ X, ((MulAut.conj (x₀ : C) * β₁)⁻¹ * β₂) y = y := fun y hy => by
    have h1 : β₂ y = (MulAut.conj (x₀ : C) * β₁) y := by
      have h2 := congrArg (fun θ : MulAut ↥X => ((θ ⟨y, hy⟩ : ↥X) : C)) hθ'
      simp only [hθ₂, coe_restrictAutOfMapsTo, MulAut.mul_apply, MulAut.conj_apply,
        hθ₁] at h2
      rw [h2, MulAut.mul_apply, MulAut.conj_apply]
      rfl
    rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
  have h := hcen _ hfix
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  rw [← h, map_mul, hinn, one_mul]

theorem fieldRigidInOf_map_of_centralizer [Finite C] (fp : MulAut C →* (L ≃+* L))
    {X : Subgroup C} (hinn : ∀ x : C, fp (MulAut.conj x) = 1)
    (hcen : ∀ β : MulAut C, (∀ x ∈ X, β x = x) → fp β = 1) (hout : OuterCommutative X)
    (δ₁ δ₂ : MulAut C) : FieldRigidInOf fp (X.map δ₁.toMonoidHom) (X.map δ₂.toMonoidHom) :=
  fieldRigidInOf_map fp (fieldRigidInOf_self_of_centralizer fp hinn hcen hout) δ₁ δ₂

end Rigid

end CFSG.SeitzReduction.OmegaPilot
