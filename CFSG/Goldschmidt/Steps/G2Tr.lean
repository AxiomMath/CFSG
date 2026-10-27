module

public import CFSG.Goldschmidt.Steps.G2Semi
public import CFSG.Goldschmidt.Steps.G2Odd

public section

namespace CFSG.Goldschmidt.G2

open Module CFSG.QuasithinUnique
open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {X : Subgroup (V ≃ₗ[ZMod 2] V)} {η : V ≃ₗ[ZMod 2] V}

omit [Finite V] in
theorem irreducible_of_transitive (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) :
    ∀ S : Submodule (ZMod 2) V, (∀ x ∈ X, ∀ v ∈ S, x v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  by_cases hS0 : S = ⊥
  · exact Or.inl hS0
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  rw [Submodule.eq_top_iff']
  intro w
  by_cases hw : w = 0
  · rw [hw]
    exact S.zero_mem
  obtain ⟨x, hx, rfl⟩ := htr v w hv0 hw
  exact hS x hx v hv

namespace LinHyp

variable (h : LinHyp X η)
include h

omit [Finite V] in
theorem smul_fixSp_ne_bot (x : V ≃ₗ[ZMod 2] V) : x • fixSp η ≠ ⊥ := by
  intro h0
  apply h.fixSp_ne_bot
  rw [← inv_smul_smul x (fixSp η), h0, Submodule.smul_bot']

theorem semiregular_of_transitive
    (hidx : ∀ X₀ : Subgroup (V ≃ₗ[ZMod 2] V), X₀ ≤ X → (X₀.subgroupOf X).index ≠ 2)
    (hnorm : ∀ x ∈ X, x • fixSp η = fixSp η → x * η * x⁻¹ ∈ Subgroup.zpowers η)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) :
    ∀ x ∈ X, x • fixSp η ≠ fixSp η → ∀ k : ℕ,
      (η ^ k) • (x • fixSp η) = x • fixSp η → η ^ k = 1 := by
  intro x hx hxW k hk
  by_contra hk1
  have hg : η ^ k ∈ Subgroup.zpowers η := Subgroup.npow_mem_zpowers η k
  have hW₁g : ∀ u ∈ x • fixSp η, (η ^ k) u ∈ x • fixSp η := by
    intro u hu
    rw [← hk]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hu
  have hW₁D : x • fixSp η ≤ comSp η := by
    let φ : ↥(x • fixSp η) → ↥(x • fixSp η) := fun u =>
      ⟨(η ^ k) u - u, (x • fixSp η).sub_mem (hW₁g u u.2) u.2⟩
    have hφ : Function.Injective φ := by
      intro u u' huu
      have h1 : (η ^ k) u - u = (η ^ k) u' - u' := congrArg Subtype.val huu
      have h2 : (η ^ k) ((u : V) - u') = u - u' := by
        rw [map_sub]
        rw [sub_eq_sub_iff_sub_eq_sub] at h1
        exact h1
      have h3 : (u : V) - u' ∈ fixSp η := h.mem_fixSp_of_apply_eq hg hk1 h2
      have h4 : (u : V) - u' ∈ x • fixSp η ⊓ fixSp η :=
        Submodule.mem_inf.mpr ⟨(x • fixSp η).sub_mem u.2 u'.2, h3⟩
      rw [h.ti x hx hxW, Submodule.mem_bot, sub_eq_zero] at h4
      exact Subtype.ext h4
    intro w hw
    obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨w, hw⟩
    have : (η ^ k) u - u = w := congrArg Subtype.val hu
    rw [← this]
    exact h.sub_mem_comSp hg u
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.smul_fixSp_ne_bot x)
  have hcase : ∀ x' ∈ X, x' • fixSp η ⊓ comSp η ≠ ⊥ → x' • fixSp η ≤ comSp η := by
    intro x' hx' hne
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨hdx', hdD⟩ := Submodule.mem_inf.mp hd
    obtain ⟨i, hi⟩ := h.trans w₁ (hW₁D hw₁) d hdD hw₁0 hd0
    have heq : (η ^ i * x) • fixSp η = x' • fixSp η := by
      refine h.smul_eq_of_inf_ne_bot (X.mul_mem (X.pow_mem h.mem i) hx) hx' fun hbot => hd0 ?_
      have hmem : d ∈ (η ^ i * x) • fixSp η ⊓ x' • fixSp η := by
        refine Submodule.mem_inf.mpr ⟨?_, hdx'⟩
        rw [mul_smul, ← hi]
        exact Submodule.smul_mem_pointwise_smul _ _ _ hw₁
      rwa [hbot, Submodule.mem_bot] at hmem
    rw [← heq, mul_smul]
    rintro _ ⟨u, hu, rfl⟩
    exact apply_mem_comSp (mul_comm_of_mem_zpowers (Subgroup.npow_mem_zpowers η i)) (hW₁D hu)
  have hodd := h.odd_card hidx hnorm htr hcase
  have hgW : (x⁻¹ * η ^ k * x) • fixSp η = fixSp η := by
    rw [mul_smul, mul_smul, hk, inv_smul_smul]
  have hgX : x⁻¹ * η ^ k * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx) (X.pow_mem h.mem k)) hx
  have hgN := hnorm _ hgX hgW
  have hxW' : ∀ w ∈ fixSp η, x⁻¹ w ∈ comSp η := by
    intro w hw
    obtain ⟨d, hd, w', hw', hdw⟩ := h.exists_add (x⁻¹ w)
    have h1 : (x⁻¹ * η ^ k * x) (x⁻¹ w) = x⁻¹ w := by
      simp only [LinearEquiv.mul_apply]
      rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, ← LinearEquiv.coe_inv,
        apply_eq_of_mem_zpowers hg hw]
    have h2 : (x⁻¹ * η ^ k * x) d ∈ comSp η := h.apply_mem_comSp_of_normalizes hgN hd
    have h3 : (x⁻¹ * η ^ k * x) w' ∈ fixSp η := by
      rw [← hgW]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hw'
    rw [← hdw, map_add] at h1
    have h4 := (h.add_inj h2 hd h3 hw' h1).2
    have h5 : (η ^ k) (x w') = x w' := by
      have := congrArg x h4
      simpa [LinearEquiv.mul_apply] using this
    have h6 : x w' ∈ x • fixSp η ⊓ fixSp η :=
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem_pointwise_smul _ _ _ hw',
        h.mem_fixSp_of_apply_eq hg hk1 h5⟩
    rw [h.ti x hx hxW, Submodule.mem_bot] at h6
    have hw'0 : w' = 0 := by simpa using congrArg x.symm h6
    rw [← hdw, hw'0, add_zero]
    exact hd
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixSp_ne_bot
  have hu0 : x⁻¹ w₀ ≠ 0 := fun h0 => hw₀0 (by simpa using congrArg x h0)
  obtain ⟨i, hi⟩ := h.trans w₁ (hW₁D hw₁) (x⁻¹ w₀) (hxW' w₀ hw₀) hw₁0 hu0
  have heq : (η ^ i * x) • fixSp η = x⁻¹ • fixSp η := by
    refine h.smul_eq_of_inf_ne_bot (X.mul_mem (X.pow_mem h.mem i) hx) (X.inv_mem hx)
      fun hbot => hu0 ?_
    have hmem : x⁻¹ w₀ ∈ (η ^ i * x) • fixSp η ⊓ x⁻¹ • fixSp η := by
      refine Submodule.mem_inf.mpr ⟨?_, Submodule.smul_mem_pointwise_smul _ _ _ hw₀⟩
      rw [mul_smul, ← hi]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hw₁
    rwa [hbot, Submodule.mem_bot] at hmem
  let s : X := ⟨(η ^ i)⁻¹ * x⁻¹, X.mul_mem (X.inv_mem (X.pow_mem h.mem i)) (X.inv_mem hx)⟩
  have hs1 : s • fixSp η = x • fixSp η := by
    show ((η ^ i)⁻¹ * x⁻¹) • fixSp η = x • fixSp η
    rw [mul_smul, ← heq, mul_smul, inv_smul_smul]
  have hs2 : s • (x • fixSp η) = fixSp η := by
    show ((η ^ i)⁻¹ * x⁻¹) • (x • fixSp η) = fixSp η
    rw [mul_smul, inv_smul_smul, smul_fixSp_of_mem_zpowers (Subgroup.inv_mem _
      (Subgroup.npow_mem_zpowers η i))]
  have := smul_eq_of_sq_smul_eq hodd s (fixSp η) (by rw [hs1, hs2])
  rw [hs1] at this
  exact hxW this

end LinHyp

end CFSG.Goldschmidt.G2
