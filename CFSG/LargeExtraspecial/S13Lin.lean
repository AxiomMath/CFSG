module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LargeExtraspecial.S13

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_neg_eq (x : V) : -x = x := by
  have h : (2 : ZMod 2) • x = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [two_smul] at h
  exact neg_eq_of_add_eq_zero_left h

theorem fix_of_fix_sq {k : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1) {v : V} (hv : k (k v) = v) :
    k v = v := by
  have h3 : k (k (k v)) = v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hk3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  rw [hv] at h3
  exact h3

theorem inf_map_eq_bot_of_le_fixSpace {k τ : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1)
    (hfpf : ∀ v, k v = v → v = 0) (hinv : τ * k = k⁻¹ * τ) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, τ w = w) : W ⊓ W.map (k : V →ₗ[ZMod 2] V) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvW, w, hwW, rfl⟩
  rw [Submodule.mem_bot]
  have h1 : τ (k w) = k w := hW _ hvW
  have h2 : τ (k w) = k⁻¹ (τ w) := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f w) hinv
    simpa [LinearEquiv.mul_apply] using this
  rw [hW w hwW] at h2
  have h3 : k⁻¹ w = k w := h2.symm.trans h1
  have h4 : k (k w) = w := by
    have := congrArg k h3
    rw [show k (k⁻¹ w) = w from k.apply_symm_apply w] at this
    exact this.symm
  have h5 := hfpf w (fix_of_fix_sq hk3 h4)
  change k w = 0
  rw [h5, map_zero]

theorem fixSpace_inf_map_eq_bot {k τ : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1)
    (hfpf : ∀ v, k v = v → v = 0) (hinv : τ * k = k⁻¹ * τ) :
    fixSpace τ ⊓ (fixSpace τ).map (k : V →ₗ[ZMod 2] V) = ⊥ :=
  inf_map_eq_bot_of_le_fixSpace hk3 hfpf hinv fun _ hw => mem_fixSpace.mp hw

theorem commSpace_le_fixSpace {τ : V ≃ₗ[ZMod 2] V} (hττ : τ * τ = 1) :
    commSpace τ ≤ fixSpace τ := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  rw [mem_fixSpace, map_sub]
  have h : τ (τ v) = v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hττ
    simpa [LinearEquiv.mul_apply] using this
  rw [h, ← neg_sub, zmod2_neg_eq]

variable [FiniteDimensional (ZMod 2) V]

theorem two_mul_finrank_fixSpace_of_inverts {k τ : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1)
    (hfpf : ∀ v, k v = v → v = 0) (hττ : τ * τ = 1) (hinv : τ * k = k⁻¹ * τ) :
    2 * finrank (ZMod 2) (fixSpace τ) = finrank (ZMod 2) V := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace τ)
    ((fixSpace τ).map (k : V →ₗ[ZMod 2] V))
  rw [fixSpace_inf_map_eq_bot hk3 hfpf hinv, finrank_bot, add_zero,
    LinearEquiv.finrank_map_eq] at h1
  have h2 := Submodule.finrank_le (fixSpace τ ⊔ (fixSpace τ).map (k : V →ₗ[ZMod 2] V))
  have h3 := finrank_commSpace_add_finrank_fixSpace τ
  have h4 := Submodule.finrank_mono (commSpace_le_fixSpace hττ)
  omega

theorem two_mul_finrank_commSpace_of_inverts {k τ : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1)
    (hfpf : ∀ v, k v = v → v = 0) (hττ : τ * τ = 1) (hinv : τ * k = k⁻¹ * τ) :
    2 * finrank (ZMod 2) (commSpace τ) = finrank (ZMod 2) V := by
  have h1 := two_mul_finrank_fixSpace_of_inverts hk3 hfpf hττ hinv
  have h3 := finrank_commSpace_add_finrank_fixSpace τ
  omega

end CFSG.LargeExtraspecial.S13
