module

public import CFSG.LargeExtraspecial.DWCaseIIHCocycle

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting CFSG.ClassicalGroups.Alternating
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ω : BilinForm (ZMod 2) V}

theorem exists_isotropic_triple (hnd : ω.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) : ∃ a b c : V, ω a b = 0 ∧ ω a c = 0 ∧ ω b c = 0 ∧ a ≠ 0 ∧
      b ∉ span (ZMod 2) {a} ∧ c ∉ span (ZMod 2) {a, b} := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  have hlt1 : finrank (ZMod 2) (span (ZMod 2) {a}) <
      finrank (ZMod 2) (ω.orthogonal (span (ZMod 2) {a})) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha]
    omega
  obtain ⟨b, hb, hba⟩ := exists_mem_notMem_of_finrank_lt hlt1
  have hlt2 : finrank (ZMod 2) (span (ZMod 2) {a, b}) <
      finrank (ZMod 2) (ω.orthogonal (span (ZMod 2) {a, b})) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd]
    have := finrank_span_pair_le a b
    omega
  obtain ⟨c, hc, hcab⟩ := exists_mem_notMem_of_finrank_lt hlt2
  refine ⟨a, b, c, ?_, ?_, ?_, ha, hba, hcab⟩
  · exact LinearMap.BilinForm.mem_orthogonal_iff.mp hb a (mem_span_singleton_self a)
  · exact LinearMap.BilinForm.mem_orthogonal_iff.mp hc a (subset_span (by simp))
  · exact LinearMap.BilinForm.mem_orthogonal_iff.mp hc b (subset_span (by simp))

omit [FiniteDimensional (ZMod 2) V] in
theorem symplecticTransvection_apply_eq_tv (hω : ω.IsAlt) (a : V) (c : ZMod 2) (x : V) :
    (symplecticTransvection ω hω a c : V →ₗ[ZMod 2] V) x = tv ω (c • a) x := by
  rw [symplecticTransvection_apply, tv_apply, map_smul, smul_smul, smul_eq_mul]
  rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp

namespace IsSpCocycle

variable {L : Type*} [Group L] {ρ : L →* (V ≃ₗ[ZMod 2] V)} {δ : L → Module.End (ZMod 2) V}

theorem exists_eq_conjE_add (H : IsSpCocycle ω ρ δ) (hω : ω.IsAlt) (hnd : ω.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) :
    ∃ w : Module.End (ZMod 2) V, IsAltEnd ω w ∧ ∀ g, δ g = conjE (ρ g) w + w := by
  obtain ⟨α, e, hd⟩ := H.exists_tvData hω hnd (by omega)
  obtain ⟨a, w, hw, hD⟩ := hd.exists_isAltEnd hω hnd h6
  refine ⟨w, hw, fun g => ?_⟩
  set δ' : L → Module.End (ZMod 2) V := fun g => δ g + (conjE (ρ g) w + w) with hδ'
  have hcoc : ∀ g h, δ' (g * h) = δ' g + conjE (ρ g) (δ' h) := by
    intro g h
    simp only [hδ', H.cocycle, conjE_add, map_mul, conjE_mul]
    abel_two
  have hker' : ∀ g, ρ g = 1 → δ' g = 0 := by
    intro g hg
    simp only [hδ', H.ker g hg, hg, conjE_one, ZModModule.add_self]
  have hcongr' : ∀ g g', ρ g = ρ g' → δ' g = δ' g' := by
    intro g g' h
    have h1 : ρ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hcoc g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hker' _ h1, conjE_zero, add_zero] at h2
    exact h2.symm
  have hlift : ∀ v, v ≠ 0 → δ' (H.lift v) = a • 1 := by
    intro v hv
    simp only [hδ']
    rw [← H.tvVal_eq, hD v hv, H.conjE_lift hω v hw]
    abel_two
  have hone : δ' 1 = 0 := hker' 1 (map_one ρ)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have ha : a = 0 := by
    obtain ⟨x, y, z, hxy, hxz, hyz, hx, hyx, hzxy⟩ := exists_isotropic_triple hnd h6
    have hy : y ≠ 0 := fun h => hyx (h ▸ zero_mem _)
    have hxy0 : x + y ≠ 0 := fun h => hyx (by
      rw [← vec_eq_of_add_eq_zero h]
      exact mem_span_singleton_self x)
    have hmem : ∀ c : V, c ∈ span (ZMod 2) {x, y} → c + z ≠ 0 := fun c hc h => hzxy (by
      rw [← vec_eq_of_add_eq_zero h]
      exact hc)
    have hz : z ≠ 0 := by simpa using hmem 0 (zero_mem _)
    have hxz0 : x + z ≠ 0 := hmem x (subset_span (by simp))
    have hyz0 : y + z ≠ 0 := hmem y (subset_span (by simp))
    have hxyz0 : x + y + z ≠ 0 :=
      hmem (x + y) (add_mem (subset_span (by simp)) (subset_span (by simp)))
    have h1 := hcongr' _ _ (H.lift_four hω hxy hxz hyz)
    rw [hcoc, hcoc, hcoc, hcoc, hcoc, hlift x hx, hlift y hy, hlift z hz, hlift _ hxyz0,
      hlift _ hxz0, hlift _ hyz0, hlift _ hxy0] at h1
    simp only [conjE_add, conjE_smul_one] at h1
    have h2 : a • (1 : Module.End (ZMod 2) V) = 0 := by
      have h3 : a • (1 : Module.End (ZMod 2) V) =
          (a • 1 + (a • 1 + (a • 1 + a • 1))) + (a • 1 + (a • 1 + a • 1)) := by
        abel_two
      rw [h3, h1, ZModModule.add_self]
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    have h4 := LinearMap.congr_fun h2 v₀
    rw [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at h4
    rcases smul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd h hv₀
  have hlift0 : ∀ v, δ' (H.lift v) = 0 := by
    intro v
    by_cases hv : v = 0
    · refine hker' _ (LinearEquiv.ext fun x => ?_)
      rw [H.lift_apply, hv, tv_apply, smul_zero, add_zero]
      rfl
    · rw [hlift v hv, ha, zero_smul]
  let toGL := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
  have key : ∀ f ∈ Subgroup.closure
      {f | ∃ (b : V) (c : ZMod 2), f = symplecticTransvection ω hω b c},
      ∃ l, δ' l = 0 ∧ toGL (ρ l) = f := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      obtain ⟨b, c, rfl⟩ := hf
      refine ⟨H.lift (c • b), hlift0 _, Units.ext (LinearMap.ext fun x => ?_)⟩
      rw [symplecticTransvection_apply_eq_tv hω]
      exact H.lift_apply (c • b) x
    | one => exact ⟨1, hone, by rw [map_one, map_one]⟩
    | mul f₁ f₂ _ _ ih₁ ih₂ =>
      obtain ⟨l₁, h₁, e₁⟩ := ih₁
      obtain ⟨l₂, h₂, e₂⟩ := ih₂
      exact ⟨l₁ * l₂, by rw [hcoc, h₁, h₂, conjE_zero, add_zero], by rw [map_mul, map_mul, e₁, e₂]⟩
    | inv f _ ih =>
      obtain ⟨l, hl, el⟩ := ih
      refine ⟨l⁻¹, ?_, by rw [map_inv, map_inv, el]⟩
      have h1 := hcoc l⁻¹ l
      rw [inv_mul_cancel, hone, hl, conjE_zero, add_zero] at h1
      exact h1.symm
  have hmem : toGL (ρ g) ∈ Subgroup.closure
      {f | ∃ (b : V) (c : ZMod 2), f = symplecticTransvection ω hω b c} := by
    rw [← alternating_transvection_generation hω hnd]
    exact fun x y => H.isometry g x y
  obtain ⟨l, hl, hle⟩ := key _ hmem
  have hg : δ' g = 0 := by
    rw [← hcongr' l g (toGL.injective hle)]
    exact hl
  exact vec_eq_of_add_eq_zero hg

end IsSpCocycle

end CFSG.LargeExtraspecial.DW
