module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem eq_zero_or_eq_of_ker_le {φ ψ : Dual (ZMod 2) E} (hψ : ψ ≠ 0)
    (h : LinearMap.ker ψ ≤ LinearMap.ker φ) : φ = 0 ∨ φ = ψ := by
  obtain ⟨e, he⟩ : ∃ e, ψ e = 1 := by
    by_contra! hne
    refine hψ (LinearMap.ext fun v => ?_)
    rcases zmod_two_eq_zero_or_one (ψ v) with h0 | h1
    · exact h0
    · exact absurd h1 (hne v)
  have key : ∀ v, φ v = ψ v * φ e := by
    intro v
    have hv : v + ψ v • e ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_add, map_smul, he, smul_eq_mul, mul_one, zmod_two_add_self]
    have := h hv
    rw [LinearMap.mem_ker, map_add, map_smul, smul_eq_mul] at this
    exact (two_add_eq_iff.mp this).trans (zero_add _)
  rcases zmod_two_eq_zero_or_one (φ e) with h0 | h1
  · exact Or.inl (LinearMap.ext fun v => by rw [key, h0, mul_zero]; rfl)
  · exact Or.inr (LinearMap.ext fun v => by rw [key, h1, mul_one])

@[expose] def goodAxes (T : Subgroup (E ≃ₗ[ZMod 2] E)) : Submodule (ZMod 2) (Dual (ZMod 2) E) where
  carrier := {φ | ∀ d, φ d = 0 → ∃ t ∈ T, ∀ x, t x = x + φ x • d}
  zero_mem' d _ := ⟨1, T.one_mem, fun x => by rw [LinearMap.zero_apply, zero_smul, add_zero]; rfl⟩
  add_mem' {φ ψ} hφ hψ d hd := by
    by_cases hψ0 : ψ = 0
    · subst hψ0
      rw [add_zero] at hd ⊢
      exact hφ d hd
    by_cases hφ0 : φ = 0
    · subst hφ0
      rw [zero_add] at hd ⊢
      exact hψ d hd
    by_cases hφψ : φ = ψ
    · subst hφψ
      exact ⟨1, T.one_mem, fun x => by
        rw [LinearMap.add_apply, zmod_two_add_self, zero_smul, add_zero]; rfl⟩
    obtain ⟨e, hψe, hφe⟩ : ∃ e, ψ e = 0 ∧ φ e = 1 := by
      by_contra! hne
      have hle : LinearMap.ker ψ ≤ LinearMap.ker φ := fun v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rcases zmod_two_eq_zero_or_one (φ v) with h0 | h1
        · exact h0
        · exact absurd h1 (hne v hv)
      rcases eq_zero_or_eq_of_ker_le hψ0 hle with h | h
      · exact hφ0 h
      · exact hφψ h
    obtain ⟨t₁, ht₁, ht₁x⟩ := hψ e hψe
    have ht₁t₁ : ∀ x, t₁ (t₁ x) = x := fun x => by
      rw [ht₁x, ht₁x, map_add, map_smul, hψe, smul_zero, add_zero, add_assoc, ← add_smul,
        zmod_two_add_self, zero_smul, add_zero]
    have hφt₁ : ∀ x, φ (t₁ x) = (φ + ψ) x := fun x => by
      rw [ht₁x, map_add, map_smul, hφe, smul_eq_mul, mul_one, LinearMap.add_apply]
    have ht₁inv : ∀ x, (t₁⁻¹ : E ≃ₗ[ZMod 2] E) x = t₁ x := fun x => by
      change t₁.symm x = t₁ x
      rw [LinearEquiv.symm_apply_eq, ht₁t₁]
    obtain ⟨t₂, ht₂, ht₂x⟩ := hφ (t₁ d) (by rw [hφt₁, hd])
    refine ⟨t₁⁻¹ * t₂ * t₁, T.mul_mem (T.mul_mem (T.inv_mem ht₁) ht₂) ht₁, fun x => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht₂x, ht₁inv, map_add, map_smul, ht₁t₁,
      ht₁t₁, hφt₁]
  smul_mem' c φ hφ d hd := by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · exact ⟨1, T.one_mem, fun x => by
        rw [zero_smul, LinearMap.zero_apply, zero_smul, add_zero]; rfl⟩
    · rw [one_smul] at hd ⊢
      exact hφ d hd

theorem eq_top_of_axes [FiniteDimensional (ZMod 2) E] (T : Subgroup (E ≃ₗ[ZMod 2] E))
    (Φ : Set (Dual (ZMod 2) E)) (hΦ : ∀ v, (∀ φ ∈ Φ, φ v = 0) → v = 0)
    (h : ∀ φ ∈ Φ, ∀ d, φ d = 0 → ∃ t ∈ T, ∀ x, t x = x + φ x • d) : T = ⊤ := by
  have htop : goodAxes T = ⊤ := by
    by_contra hne
    obtain ⟨ψ, -, hψ⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    obtain ⟨Λ, hΛ, hΛψ⟩ := exists_dual_eq_one_of_notMem hψ
    set v := (Module.evalEquiv (ZMod 2) E).symm Λ
    have hv : ∀ f : Dual (ZMod 2) E, f v = Λ f := fun f => by
      conv_rhs => rw [← (Module.evalEquiv (ZMod 2) E).apply_symm_apply Λ]
      rfl
    have hv0 : v = 0 := hΦ v fun φ hφ => by rw [hv]; exact hΛ φ (h φ hφ)
    rw [← hv, hv0, map_zero] at hΛψ
    exact zero_ne_one hΛψ
  rw [eq_top_iff, ← closure_transvections_eq_top, Subgroup.closure_le]
  rintro e ⟨f, d, hfd, rfl⟩
  have hf : f ∈ goodAxes T := by rw [htop]; exact Submodule.mem_top
  obtain ⟨t, ht, htx⟩ := hf d hfd
  have he : LinearEquiv.transvection hfd = t :=
    LinearEquiv.ext fun x => by rw [transvection_apply, htx x]
  rw [SetLike.mem_coe, he]
  exact ht

theorem card_le_of_forall_fix [Finite E] {φ : Dual (ZMod 2) E} (hφ : φ ≠ 0)
    (H : Subgroup (E ≃ₗ[ZMod 2] E)) (hH : ∀ g ∈ H, ∀ w, φ w = 0 → g w = w) :
    Nat.card H ≤ Nat.card (LinearMap.ker φ) := by
  obtain ⟨e, he⟩ : ∃ e, φ e = 1 := by
    by_contra! hne
    refine hφ (LinearMap.ext fun v => ?_)
    rcases zmod_two_eq_zero_or_one (φ v) with h0 | h1
    · exact h0
    · exact absurd h1 (hne v)
  have hmem : ∀ g : H, (g : E ≃ₗ[ZMod 2] E) e - e ∈ LinearMap.ker φ := by
    intro g
    rw [LinearMap.mem_ker, map_sub, he]
    rcases zmod_two_eq_zero_or_one (φ ((g : E ≃ₗ[ZMod 2] E) e)) with h0 | h1
    · exfalso
      have := hH _ g.2 _ h0
      have hfix : (g : E ≃ₗ[ZMod 2] E) ((g : E ≃ₗ[ZMod 2] E) e) =
          (g : E ≃ₗ[ZMod 2] E) e := this
      rw [(g : E ≃ₗ[ZMod 2] E).injective hfix] at h0
      rw [he] at h0
      exact one_ne_zero h0
    · rw [h1, sub_self]
  have hinj : Function.Injective fun g : H => (⟨_, hmem g⟩ : LinearMap.ker φ) := by
    intro g g' hgg'
    have h1 : (g : E ≃ₗ[ZMod 2] E) e = (g' : E ≃ₗ[ZMod 2] E) e := by
      have := congrArg Subtype.val hgg'
      simpa using this
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have hv : v - φ v • e ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
    have hg := hH _ g.2 _ hv
    have hg' := hH _ g'.2 _ hv
    rw [map_sub, map_smul] at hg hg'
    calc (g : E ≃ₗ[ZMod 2] E) v = v - φ v • e + φ v • (g : E ≃ₗ[ZMod 2] E) e := by
          rw [← hg]; abel
      _ = v - φ v • e + φ v • (g' : E ≃ₗ[ZMod 2] E) e := by rw [h1]
      _ = (g' : E ≃ₗ[ZMod 2] E) v := by rw [← hg']; abel
  exact Nat.card_le_card_of_injective _ hinj

theorem fix_of_commute_transvections {φ : Dual (ZMod 2) E} (hφ : φ ≠ 0)
    (g : E ≃ₗ[ZMod 2] E) (hg : ∀ c (hc : φ c = 0),
      g * LinearEquiv.transvection hc = LinearEquiv.transvection hc * g)
    {w : E} (hw : φ w = 0) : g w = w := by
  obtain ⟨e, he⟩ : ∃ e, φ e = 1 := by
    by_contra! hne
    refine hφ (LinearMap.ext fun v => ?_)
    rcases zmod_two_eq_zero_or_one (φ v) with h0 | h1
    · exact h0
    · exact absurd h1 (hne v)
  have h1 := LinearEquiv.congr_fun (hg w hw) (g.symm e)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply, transvection_apply,
    map_add, map_smul, LinearEquiv.apply_symm_apply] at h1
  have h2 := add_left_cancel h1
  rcases zmod_two_eq_zero_or_one (φ (g.symm e)) with h0 | h0
  · rw [h0, zero_smul, he, one_smul] at h2
    rw [← h2, map_zero]
  · rw [h0, one_smul, he, one_smul] at h2
    exact h2

end CFSG.LargeExtraspecial.DW
