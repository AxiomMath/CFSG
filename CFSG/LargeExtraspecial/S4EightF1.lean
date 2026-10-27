module

public import CFSG.LargeExtraspecial.S4EightG
public import CFSG.LargeExtraspecial.OrthoF2Basic
public import CFSG.LargeExtraspecial.S4Span
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_fixSub_map_conj (x : S.O) (X : Subgroup S.O) {v : S.Qt} :
    v ∈ fixSub S (X.map (MulAut.conj x).toMonoidHom) ↔
      ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ fixSub S X := by
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro hv y hy
    have := hv _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have h2 := congrArg ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) this
    rw [← coe_mul_apply, show x⁻¹ * (x * y * x⁻¹) = y * x⁻¹ by group, coe_mul_apply] at h2
    exact h2
  · rintro hv _ ⟨y, hy, rfl⟩
    have := hv y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [coe_mul_apply, coe_mul_apply, this, apply_inv_apply_O]

variable (H : Hyp4 S g)
include H

theorem fixSub_Lbar_map_conj (x : S.O) :
    fixSub S ((S.Lbar g).map (MulAut.conj x).toMonoidHom) =
      (ZMod 2) ∙ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  ext v
  rw [mem_fixSub_map_conj, H.fixSub_eq, mem_span_cl_iff, mem_span_cl_iff]
  constructor
  · rintro (h | h)
    · left
      have := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h
      rwa [apply_inv_apply_O, map_zero] at this
    · right
      have := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h
      rwa [apply_inv_apply_O] at this
  · rintro (rfl | rfl)
    · left
      exact map_zero _
    · right
      exact inv_apply_apply_O _ _

variable {t : S.O} {F : Subgroup S.O} (hFodd : Odd (Nat.card F))
  (hFR : F ≤ Rbar S g t) (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
  (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1)
include hFodd hFR hLF hCF

theorem eq_one_of_mem_of_apply_eq {f : S.O} (hf : f ∈ F)
    (hfa : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) : f = 1 := by
  have hfN : f ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne
      (Rbar_le_Mbar (hFR hf)) (by simpa using hfa)
    simpa using this
  exact hCF f hf fun l hl =>
    commute_of_mem_normalizer hFodd (isPGroup_Lbar S H.conj_mem) hLF hf hfN hl

theorem eq_of_mem_of_apply_eq {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (h : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) : f₁ = f₂ := by
  have h1 := eq_one_of_mem_of_apply_eq H hFodd hFR hLF hCF (mul_mem (inv_mem hf₂) hf₁)
    (by rw [coe_mul_apply, h, inv_apply_apply_O])
  rw [← mul_left_cancel_iff (a := f₂⁻¹), h1, inv_mul_cancel]

omit hFR hCF in
theorem exists_apply_eq_add {f₁ f₂ y : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hy : y ∈ (S.Lbar g).map (MulAut.conj f₁).toMonoidHom)
    (hyc : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
        (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) :
    ∃ f ∈ F, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
        (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  have hL2 := isPGroup_Lbar S H.conj_mem
  have hLsup : S.Lbar g ≤ F ⊔ S.Lbar g := le_sup_right
  have hFsup : F ≤ F ⊔ S.Lbar g := le_sup_left
  have hyS : y ∈ F ⊔ S.Lbar g := by
    obtain ⟨l, hl, rfl⟩ := hy
    exact mul_mem (mul_mem (hFsup hf₁) (hLsup hl)) (inv_mem (hFsup hf₁))
  set P := ((S.Lbar g).map (MulAut.conj f₂).toMonoidHom).map (MulAut.conj y).toMonoidHom
    with hP
  have hPle : P ≤ F ⊔ S.Lbar g := by
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact mul_mem (mul_mem hyS (mul_mem (mul_mem (hFsup hf₂) (hLsup hl))
      (inv_mem (hFsup hf₂)))) (inv_mem hyS)
  have hPp : IsPGroup 2 P := (hL2.map _).map _
  have hPc : Nat.card P = Nat.card (S.Lbar g) := by
    rw [hP, card_map_of_injective (MulAut.conj y).injective,
      card_map_of_injective (MulAut.conj f₂).injective]
  obtain ⟨f, hf, hPf⟩ := exists_eq_map_conj_of_card_eq hFodd hL2 hLF hPp hPle hPc
  refine ⟨f, hf, ?_⟩
  have hfix : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈ fixSub S P := by
    rw [hPf, fixSub_Lbar_map_conj H]
    exact Submodule.mem_span_singleton_self _
  rw [hP, mem_fixSub_map_conj, fixSub_Lbar_map_conj H, mem_span_cl_iff] at hfix
  rcases hfix with h0 | h1
  · exfalso
    have h2 := congrArg (y : S.Qt ≃ₗ[ZMod 2] S.Qt) h0
    rw [apply_inv_apply_O, map_zero] at h2
    have h3 := congrArg ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h2
    rw [inv_apply_apply_O, map_zero] at h3
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne h3
  · have := congrArg (y : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O, hyc] at this

omit H hFodd hFR hLF hCF in
theorem mem_span_orbitF_iff
    (hclosed : ∀ f₁ ∈ F, ∀ f₂ ∈ F, (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠
      (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) →
      ∃ f ∈ F, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) +
          (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) {u : S.Qt} :
    u ∈ Submodule.span (ZMod 2)
        {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} ↔
      u = 0 ∨ ∃ f ∈ F, u = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
  constructor
  · intro hu
    induction hu using Submodule.span_induction with
    | mem v hv => exact Or.inr hv
    | zero => exact Or.inl rfl
    | add u w _ _ hu hw =>
      rcases hu with rfl | ⟨f₁, hf₁, rfl⟩
      · rwa [zero_add]
      rcases hw with rfl | ⟨f₂, hf₂, rfl⟩
      · rw [add_zero]
        exact Or.inr ⟨f₁, hf₁, rfl⟩
      by_cases heq : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
          (f₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))
      · left
        rw [heq, OrthoF2.vec_add_self]
      · obtain ⟨f, hf, hfe⟩ := hclosed f₁ hf₁ f₂ hf₂ heq
        exact Or.inr ⟨f, hf, by rw [hfe, add_comm]⟩
    | smul c u _ hu =>
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
      · rw [zero_smul]
        exact Or.inl rfl
      · rwa [one_smul]
  · rintro (rfl | ⟨f, hf, rfl⟩)
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨f, hf, rfl⟩

omit H hFodd hFR hLF hCF in
theorem apply_mem_span_orbitF {f : S.O} (hf : f ∈ F) {u : S.Qt}
    (hu : u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))}) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Submodule.span (ZMod 2)
      {v | ∃ f ∈ F, v = (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))} := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨f', hf', rfl⟩ := hv
    exact Submodule.subset_span ⟨f * f', mul_mem hf hf', (coe_mul_apply _ _ _).symm⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

end CFSG.LargeExtraspecial.S4
