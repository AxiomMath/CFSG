module

public import CFSG.LargeExtraspecial.S10SixD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem fix_Vt_mul {x y : S.O} (Xx : Hyp10 S g x) (Xy : Hyp10 S g y) (Xxy : Hyp10 S g (x * y))
    {c : S.O} (hcx : ∀ v ∈ Vt S g x, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hcy : ∀ v ∈ Vt S g y, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ∀ v ∈ Vt S g (x * y), (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hcxy := (commSpace_t_eq Xxy.H Xxy.C Xxy.ht Xxy.ht1 Xxy.hVQ).1
  have hcx' := (commSpace_t_eq Xx.H Xx.C Xx.ht Xx.ht1 Xx.hVQ).1
  have hcy' := (commSpace_t_eq Xy.H Xy.C Xy.ht Xy.ht1 Xy.hVQ).1
  intro v hv
  rw [← hcxy] at hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  have e : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) +
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
    abel
  have h1 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g y :=
    apply_mem_Vt_of_mem_Rbar Xy.haQ (Lbar_le_Rbar Xy.ht Xx.ht)
      (hcy' ▸ sub_mem_commSpace _ w)
  have h2 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g x := hcx' ▸ sub_mem_commSpace _ w
  rw [e, map_add, hcy _ h1, hcx _ h2]

theorem mem_Nbar_or (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) {m : S.M} (hm : S.ρ m ∈ Nbar S g t)
    (hmτ : S.ρ m * τ * (S.ρ m)⁻¹ = τ * t) {x₁ x : S.O} (hx₁ : x₁ ∈ S.Lbar g ⊓ Nbar S g τ)
    (hx₁N : x₁ ∉ Nbar S g t) (hxL : x ∈ S.Lbar g) (hxx : x₁⁻¹ * x ∈ Nbar S g t) :
    x ∈ Nbar S g τ ∨ x ∈ Nbar S g (τ * t) := by
  have Y := X.conj' hk hτ
  have hmL : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) :=
    Nbar_le_normalizer X.haQ X.H.conj_ne (Lbar_mem_Dset X.ht) hm
  have hkm : S.ρ (m * k) ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [map_mul]
    exact mul_mem hmL hk
  have hτ' : τ * t = S.ρ (m * k) * t * (S.ρ (m * k))⁻¹ := by
    rw [map_mul, mul_inv_rev, ← hmτ, hτ]
    group
  have Y' := X.conj' hkm hτ'
  have hNc' : Nbar S g (τ * t) = (Nbar S g τ).map (cK S m) := by
    rw [← hmτ]
    exact Nbar_conj X.haQ m τ
  have hmt : S.ρ m * t = t * S.ρ m := commute_of_mem_Rbar X.haQ (Nbar_le_Rbar hm)
  set x₂ := S.ρ m * x₁ * (S.ρ m)⁻¹ with hx₂
  have hx₂L : x₂ ∈ S.Lbar g := (mem_normalizer_iff.mp hmL x₁).mp hx₁.1
  have hx₂N' : x₂ ∈ Nbar S g (τ * t) := by
    rw [hNc', mem_map_cK_iff, hx₂]
    simpa [mul_assoc] using hx₁.2
  have hx₂N : x₂ ∉ Nbar S g t := by
    intro h
    apply hx₁N
    have hmt' : S.ρ m⁻¹ * t = t * S.ρ m⁻¹ := by
      rw [map_inv]
      calc (S.ρ m)⁻¹ * t = (S.ρ m)⁻¹ * (t * S.ρ m) * (S.ρ m)⁻¹ := by group
        _ = (S.ρ m)⁻¹ * (S.ρ m * t) * (S.ρ m)⁻¹ := by rw [hmt]
        _ = t * (S.ρ m)⁻¹ := by group
    have := conj_mem_Nbar X.haQ hmt' h
    simpa [hx₂, map_inv, mul_assoc] using this
  have hx₁R := Lbar_le_Rbar X.ht hx₁.1
  have ha₀ : x₂⁻¹ * x₁ ∈ Nbar S g t := by
    obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (inv_mem hx₁R))
    have hjt : S.ρ j * t = t * S.ρ j := by
      rw [hj]
      exact commute_of_mem_Rbar X.haQ (inv_mem hx₁R)
    have h1 := conj_mem_Nbar X.haQ hjt (inv_mem hm)
    rw [hj, inv_inv] at h1
    have e : x₂⁻¹ * x₁ = S.ρ m * (x₁⁻¹ * (S.ρ m)⁻¹ * x₁) := by
      rw [hx₂]
      group
    rw [e]
    exact mul_mem hm h1
  have hC : ∀ c ∈ S.Lbar g, c ∈ Nbar S g t → c ∈ Nbar S g τ → c ∈ Nbar S g (τ * t) :=
    fun c hcL hcN hcNτ => mem_Nbar.mpr ⟨Lbar_le_Rbar Y'.ht hcL,
      fix_Vt_mul Y X Y' (mem_Nbar.mp hcNτ).2 (mem_Nbar.mp hcN).2⟩
  have hττt : τ * (τ * t) = t := by
    rw [← mul_assoc, S4.mul_self_of_mem_Lbar S X.haQ Y.ht, one_mul]
  have hD : ∀ c ∈ S.Lbar g, c ∈ Nbar S g τ → c ∈ Nbar S g (τ * t) → c ∈ Nbar S g t := by
    intro c hcL hcNτ hcNτt
    refine mem_Nbar.mpr ⟨Lbar_le_Rbar X.ht hcL, ?_⟩
    have Xt : Hyp10 S g (τ * (τ * t)) := by
      rw [hττt]
      exact X
    have := fix_Vt_mul Y Y' Xt (mem_Nbar.mp hcNτ).2 (mem_Nbar.mp hcNτt).2
    rwa [hττt] at this
  set a := x₁⁻¹ * x with ha
  have haL : a ∈ S.Lbar g := mul_mem (inv_mem hx₁.1) hxL
  by_cases haτ : a ∈ Nbar S g τ
  · left
    have e : x = x₁ * a := by rw [ha]; group
    rw [e]
    exact mul_mem hx₁.2 haτ
  right
  set a₀ := x₂⁻¹ * x₁ with ha₀d
  have ha₀L : a₀ ∈ S.Lbar g := mul_mem (inv_mem hx₂L) hx₁.1
  have ha₀τ : a₀ ∉ Nbar S g τ := by
    intro h
    apply hx₂N
    refine hD x₂ hx₂L ?_ hx₂N'
    have e : x₂ = x₁ * a₀⁻¹ := by rw [ha₀d]; group
    rw [e]
    exact mul_mem hx₁.2 (inv_mem h)
  have hprod : a₀ * a ∈ Nbar S g τ :=
    mul_mem_Nbar_of_mem hCE Y h7 X ⟨ha₀L, ha₀⟩ ⟨haL, hxx⟩ ha₀τ haτ
  have hprodt := hC _ (mul_mem ha₀L haL) (mul_mem ha₀ hxx) hprod
  have e : x = x₂ * (a₀ * a) := by rw [ha₀d, ha]; group
  rw [e]
  exact mul_mem hx₂N' hprodt

end CFSG.LargeExtraspecial.S10
