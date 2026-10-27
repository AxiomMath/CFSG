module

public import CFSG.ClassicalInvolution.Q3.Q3WAut

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {X : Type} [Group X]

theorem b0_inv (A : SL(2, F3)) : b0 A⁻¹ = (b0 A)⁻¹ := map_inv (blockSL F3 3 2 0 (by omega)) A

theorem b1_inv (B : SL(2, F3)) : b1 B⁻¹ = (b1 B)⁻¹ := map_inv (blockSL F3 3 2 1 (by omega)) B

theorem comm_of_map_comm {θ : SL(3, F3) →* X} (hθ : θ.ker ≤ Subgroup.center SL(3, F3))
    {g h : SL(3, F3)} (hc : θ g * θ h = θ h * θ g) : g * h = h * g := by
  have hk : g * h * (h * g)⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc]
    group
  have := hθ hk
  rw [center_eq_bot, Subgroup.mem_bot] at this
  exact mul_inv_eq_one.mp this

theorem alpha_xm_unip {θ θ₀ : SL(3, F3) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, F3)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, F3))
    (hlink : ∀ A : SL(2, F3), ∃ B : SL(2, F3), θ (b1 B) = θ₀ (b0 A))
    (hcomm : ∀ A B : SL(2, F3), θ (b0 A) * θ₀ (b1 B) = θ₀ (b1 B) * θ (b0 A))
    (α : SL(2, F3) ≃* SL(2, F3)) (hα : ∀ A, θ₀ (b0 (α A)) = θ (b1 A)) :
    ∃ s : F3, α (xm 1) = xp s ∨ α (xm 1) = xm s := by
  have hinj0 : Function.Injective (θ₀.comp (blockSL F3 3 2 0 (by omega))) :=
    comp_blockSL_injective hθ₀ (by omega) (by omega)
  set A := α (xm 1) with hAdef
  have hy : θ₀ (b0 A) = θ (b1 (xm 1)) := hα (xm 1)
  have hvy : θ (b0 (xp 1)) * θ (b1 (xm 1)) = θ (b1 (xm 1)) * θ (b0 (xp 1)) := by
    rw [← map_mul, ← map_mul, (comm_b0_xp_iff 1 one_ne_zero (xm 1)).2 ⟨1, rfl⟩]
  have hA3 : A ^ 3 = 1 := by
    rw [hAdef, ← map_pow, xm_one_pow_three, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    apply xm_one_ne_one
    apply α.injective
    rw [← hAdef, h, map_one]
  by_cases h01 : A 0 1 = 0
  · obtain ⟨s, hs⟩ := unip_upper A hA3 hA1 h01
    exact ⟨s, Or.inr hs⟩
  · let H : Subgroup SL(3, F3) :=
      (Subgroup.centralizer ({θ (b0 (xp 1))} : Set X)).comap θ₀
    have hmem : ∀ g : SL(3, F3), g ∈ H ↔ θ (b0 (xp 1)) * θ₀ g = θ₀ g * θ (b0 (xp 1)) := by
      intro g
      simp [H, Subgroup.mem_centralizer_iff]
    have hH1 : ∀ B : SL(2, F3), b1 B ∈ H := fun B => (hmem _).2 (hcomm (xp 1) B)
    have hH0 : b0 A ∈ H := (hmem _).2 (by rw [hy]; exact hvy)
    have hz := (hmem _).1 (b0_xp_one_mem hH1 h01 hH0)
    obtain ⟨B', hB'⟩ := hlink (xp 1)
    have hcommB' : b0 (xp 1) * b1 B' = b1 B' * b0 (xp 1) :=
      comm_of_map_comm hθ (by rw [hB']; exact hz)
    obtain ⟨s, hs⟩ := (comm_b0_xp_iff 1 one_ne_zero B').1 hcommB'
    rcases xm_cases s with h | h | h
    · exfalso
      have e : θ₀ (b0 (xp 1)) = θ₀ (b0 1) := by
        rw [← hB', hs, h]
        simp
      exact xp_one_ne_one (hinj0 e)
    · have e : θ₀ (b0 (xp 1)) = θ₀ (b0 A) := by
        rw [← hB', hs, h, hy]
      exact ⟨1, Or.inl (hinj0 e).symm⟩
    · have e : θ₀ (b0 (xp 1)) = θ₀ (b0 A⁻¹) := by
        rw [← hB', hs, h, b1_inv, b0_inv, map_inv, map_inv, hy]
      refine ⟨-1, Or.inl ?_⟩
      have h2 : A⁻¹ = xp 1 := (hinj0 e).symm
      rw [← inv_inv A, h2, xp_one_inv]

theorem alpha_xp_unip {θ θ₀ : SL(3, F3) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, F3)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, F3))
    (hlink : ∀ A : SL(2, F3), ∃ B : SL(2, F3), θ (b1 B) = θ₀ (b0 A))
    (hcomm : ∀ A B : SL(2, F3), θ (b0 A) * θ₀ (b1 B) = θ₀ (b1 B) * θ (b0 A))
    (α : SL(2, F3) ≃* SL(2, F3)) (hα : ∀ A, θ₀ (b0 (α A)) = θ (b1 A)) :
    ∃ s : F3, α (xp 1) = xp s ∨ α (xp 1) = xm s := by
  have hinj0 : Function.Injective (θ₀.comp (blockSL F3 3 2 0 (by omega))) :=
    comp_blockSL_injective hθ₀ (by omega) (by omega)
  set A := α (xp 1) with hAdef
  have hy : θ₀ (b0 A) = θ (b1 (xp 1)) := hα (xp 1)
  have hvy : θ (b0 (xm 1)) * θ (b1 (xp 1)) = θ (b1 (xp 1)) * θ (b0 (xm 1)) := by
    rw [← map_mul, ← map_mul, (comm_b0_xm_iff 1 one_ne_zero (xp 1)).2 ⟨1, rfl⟩]
  have hA3 : A ^ 3 = 1 := by
    rw [hAdef, ← map_pow, xp_one_pow_three, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    apply xp_one_ne_one
    apply α.injective
    rw [← hAdef, h, map_one]
  by_cases h10 : A 1 0 = 0
  · obtain ⟨s, hs⟩ := unip_lower A hA3 hA1 h10
    exact ⟨s, Or.inl hs⟩
  · let H : Subgroup SL(3, F3) :=
      (Subgroup.centralizer ({θ (b0 (xm 1))} : Set X)).comap θ₀
    have hmem : ∀ g : SL(3, F3), g ∈ H ↔ θ (b0 (xm 1)) * θ₀ g = θ₀ g * θ (b0 (xm 1)) := by
      intro g
      simp [H, Subgroup.mem_centralizer_iff]
    have hH1 : ∀ B : SL(2, F3), b1 B ∈ H := fun B => (hmem _).2 (hcomm (xm 1) B)
    have hH0 : b0 A ∈ H := (hmem _).2 (by rw [hy]; exact hvy)
    have hz := (hmem _).1 (b0_xm_one_mem hH1 h10 hH0)
    obtain ⟨B', hB'⟩ := hlink (xm 1)
    have hcommB' : b0 (xm 1) * b1 B' = b1 B' * b0 (xm 1) :=
      comm_of_map_comm hθ (by rw [hB']; exact hz)
    obtain ⟨s, hs⟩ := (comm_b0_xm_iff 1 one_ne_zero B').1 hcommB'
    rcases xp_cases s with h | h | h
    · exfalso
      have e : θ₀ (b0 (xm 1)) = θ₀ (b0 1) := by
        rw [← hB', hs, h]
        simp
      exact xm_one_ne_one (hinj0 e)
    · have e : θ₀ (b0 (xm 1)) = θ₀ (b0 A) := by
        rw [← hB', hs, h, hy]
      exact ⟨1, Or.inr (hinj0 e).symm⟩
    · have e : θ₀ (b0 (xm 1)) = θ₀ (b0 A⁻¹) := by
        rw [← hB', hs, h, b1_inv, b0_inv, map_inv, map_inv, hy]
      refine ⟨-1, Or.inr ?_⟩
      have h2 : A⁻¹ = xm 1 := (hinj0 e).symm
      rw [← inv_inv A, h2, xm_one_inv]

theorem coordSet_F3 {g : SL(2, F3)} (hg : g ∈ coordSet F3) :
    g = xp 1 ∨ g = (xp 1)⁻¹ ∨ g = xm 1 ∨ g = (xm 1)⁻¹ := by
  have key : ∀ g : SL(2, F3), (g ≠ 1 ∧ ∃ t : F3, g = xp t ∨ g = xm t) →
      g = xp 1 ∨ g = (xp 1)⁻¹ ∨ g = xm 1 ∨ g = (xm 1)⁻¹ := by
    decide +kernel
  exact key g hg

theorem coord_of_unip (α : SL(2, F3) ≃* SL(2, F3))
    (h₁ : ∃ s : F3, α (xp 1) = xp s ∨ α (xp 1) = xm s)
    (h₂ : ∃ s : F3, α (xm 1) = xp s ∨ α (xm 1) = xm s) :
    ∀ g ∈ coordSet F3, α g ∈ coordSet F3 := by
  have hp : α (xp 1) ∈ coordSet F3 := by
    obtain ⟨s, hs⟩ := h₁
    refine ⟨fun h => xp_one_ne_one (α.injective (by rw [h, map_one])), s, hs⟩
  have hm : α (xm 1) ∈ coordSet F3 := by
    obtain ⟨s, hs⟩ := h₂
    refine ⟨fun h => xm_one_ne_one (α.injective (by rw [h, map_one])), s, hs⟩
  intro g hg
  rcases coordSet_F3 hg with rfl | rfl | rfl | rfl
  · exact hp
  · rw [map_inv]; exact inv_mem_coordSet hp
  · exact hm
  · rw [map_inv]; exact inv_mem_coordSet hm

theorem exists_alpha3 {θ θ₀ : SL(3, F3) →* X} {V₀ V₁ V₂ : Subgroup X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, F3)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, F3))
    (h0 : (B12 F3).map θ = V₀) (h1 : (B23 F3).map θ = V₁) (h1' : (B12 F3).map θ₀ = V₁)
    (h2 : (B23 F3).map θ₀ = V₂) (hcomm : ∀ x ∈ V₀, ∀ y ∈ V₂, x * y = y * x) :
    ∃ α : SL(2, F3) ≃* SL(2, F3),
      (∀ A, θ₀ (blockSL F3 3 2 0 (by omega) (α A)) = θ (blockSL F3 3 2 1 (by omega) A)) ∧
        ∀ g ∈ coordSet F3, α g ∈ coordSet F3 := by
  have hm₁ : Function.Injective (θ.comp (blockSL F3 3 2 1 (by omega))) :=
    comp_blockSL_injective hθ _ (by omega)
  have hm₂ : Function.Injective (θ₀.comp (blockSL F3 3 2 0 (by omega))) :=
    comp_blockSL_injective hθ₀ _ (by omega)
  have hr₁ : (θ.comp (blockSL F3 3 2 1 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1]
    rfl
  have hr₂ : (θ₀.comp (blockSL F3 3 2 0 (by omega))).range = V₁ := by
    rw [MonoidHom.range_comp, ← h1']
    rfl
  have hrr : (θ.comp (blockSL F3 3 2 1 (by omega))).range =
      (θ₀.comp (blockSL F3 3 2 0 (by omega))).range := hr₁.trans hr₂.symm
  let α : SL(2, F3) ≃* SL(2, F3) :=
    (MonoidHom.ofInjective hm₁).trans
      ((MulEquiv.subgroupCongr hrr).trans (MonoidHom.ofInjective hm₂).symm)
  have hα : ∀ A, θ₀ (blockSL F3 3 2 0 (by omega) (α A)) = θ (blockSL F3 3 2 1 (by omega) A) := by
    intro A
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hm₂).apply_symm_apply
      (MulEquiv.subgroupCongr hrr (MonoidHom.ofInjective hm₁ A)))
    exact h
  have hlink : ∀ A : SL(2, F3), ∃ B : SL(2, F3), θ (b1 B) = θ₀ (b0 A) := by
    intro A
    have hA : θ₀ (b0 A) ∈ V₁ := h1' ▸ ⟨b0 A, ⟨A, rfl⟩, rfl⟩
    rw [← h1] at hA
    obtain ⟨_, ⟨B, rfl⟩, hB⟩ := hA
    exact ⟨B, hB⟩
  have hcomm' : ∀ A B : SL(2, F3), θ (b0 A) * θ₀ (b1 B) = θ₀ (b1 B) * θ (b0 A) := fun A B =>
    hcomm _ (h0 ▸ ⟨b0 A, ⟨A, rfl⟩, rfl⟩) _ (h2 ▸ ⟨b1 B, ⟨B, rfl⟩, rfl⟩)
  exact ⟨α, hα, coord_of_unip α (alpha_xp_unip hθ hθ₀ hlink hcomm' α hα)
    (alpha_xm_unip hθ hθ₀ hlink hcomm' α hα)⟩

theorem exists_adjust3 {θ θ₀ : SL(3, F3) →* X} {V₀ V₁ V₂ : Subgroup X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, F3)) (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, F3))
    (h0 : (B12 F3).map θ = V₀) (h1 : (B23 F3).map θ = V₁) (h1' : (B12 F3).map θ₀ = V₁)
    (h2 : (B23 F3).map θ₀ = V₂) (hcomm : ∀ x ∈ V₀, ∀ y ∈ V₂, x * y = y * x) :
    ∃ θ' : SL(3, F3) →* X, θ'.ker ≤ Subgroup.center SL(3, F3) ∧ (B12 F3).map θ' = V₁ ∧
      (B23 F3).map θ' = V₂ ∧
      θ'.comp (blockSL F3 3 2 0 (by omega)) = θ.comp (blockSL F3 3 2 1 (by omega)) := by
  obtain ⟨α, hα, hαC⟩ := exists_alpha3 hθ hθ₀ h0 h1 h1' h2 hcomm
  have hp : ∃ s : F3, α (xp 1) = xp s ∨ α (xp 1) = xm s := by
    obtain ⟨t, -, ht⟩ := coordSet_cases (hαC _ (xp_mem_coordSet one_ne_zero))
    exact ⟨t, ht⟩
  have hm : ∃ s : F3, α (xm 1) = xp s ∨ α (xm 1) = xm s := by
    obtain ⟨t, -, ht⟩ := coordSet_cases (hαC _ (xm_mem_coordSet one_ne_zero))
    exact ⟨t, ht⟩
  obtain ⟨β, hβ0, hβ1, -⟩ := exists_extend_unip α hp hm
  have hB12 : (B12 F3).map β.toMonoidHom = B12 F3 := by
    ext x
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨α A, (hβ0 A).symm⟩
    · rintro ⟨A, rfl⟩
      refine ⟨blockSL F3 3 2 0 (by omega) (α.symm A), ⟨_, rfl⟩, ?_⟩
      show β (blockSL F3 3 2 0 (by omega) (α.symm A)) = _
      rw [hβ0, MulEquiv.apply_symm_apply]
  refine ⟨θ₀.comp β.toMonoidHom, ker_comp_mulEquiv_le_center hθ₀ β, ?_, ?_, ?_⟩
  · rw [map_comp_mulEquiv, hB12, h1']
  · rw [map_comp_mulEquiv, hβ1, h2]
  · refine MonoidHom.ext fun A => ?_
    show θ₀ (β (blockSL F3 3 2 0 (by omega) A)) = θ (blockSL F3 3 2 1 (by omega) A)
    rw [hβ0, hα]

end CFSG.ClassicalInvolution.Q3.Q3W
