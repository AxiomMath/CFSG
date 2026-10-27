module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

variable {D Y₁ Y₂ : Type*} [Group D] [Group Y₁] [Group Y₂]

theorem not_isSolvable_of_simple [IsSimpleGroup Y₂] (hY₂ : ∃ a b : Y₂, a * b ≠ b * a) :
    ¬ Group.IsSolvable Y₂ := by
  intro hsol
  obtain ⟨a, b, hab⟩ := hY₂
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Y₂)).mpr hsol a b)

theorem ker_eq_of_solvable [IsSimpleGroup Y₁] [IsSimpleGroup Y₂]
    (hY₂ : ∃ a b : Y₂, a * b ≠ b * a) {f₁ : D →* Y₁} {f₂ : D →* Y₂}
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (hsol : Group.IsSolvable ↥f₁.ker) : f₁.ker = f₂.ker := by
  have h12 : f₁.ker ≤ f₂.ker := by
    have hn : (f₁.ker.map f₂).Normal := (MonoidHom.normal_ker f₁).map f₂ hf₂
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f₁.ker.map f₂) with hbot | htop
    · intro x hx
      have : f₂ x ∈ f₁.ker.map f₂ := Subgroup.mem_map_of_mem f₂ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply not_isSolvable_of_simple hY₂
      have hs : Group.IsSolvable ↥(f₁.ker.map f₂) :=
        Group.isSolvable_of_surjective (f₂.subgroupMap_surjective f₁.ker)
      rw [htop] at hs
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Y₂) ≃* Y₂).toMonoidHom)
        Subgroup.topEquiv.surjective
  refine le_antisymm h12 ?_
  have hn : (f₂.ker.map f₁).Normal := (MonoidHom.normal_ker f₂).map f₁ hf₁
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f₂.ker.map f₁) with hbot | htop
  · intro x hx
    have : f₁ x ∈ f₂.ker.map f₁ := Subgroup.mem_map_of_mem f₁ hx
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := hY₂
    have hall : ∀ d : D, f₂ d = 1 := by
      intro d
      have hd : f₁ d ∈ f₂.ker.map f₁ := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcd⟩ := hd
      have hc1 : c⁻¹ * d ∈ f₁.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcd, inv_mul_cancel]
      have h2 := h12 hc1
      rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.mp hc, inv_one, one_mul] at h2
      exact h2
    obtain ⟨d₁, rfl⟩ := hf₂ a
    obtain ⟨d₂, rfl⟩ := hf₂ b
    exact hab (by rw [hall d₁, hall d₂])

theorem exists_equiv_of_solvable [IsSimpleGroup Y₁] [IsSimpleGroup Y₂]
    (hY₂ : ∃ a b : Y₂, a * b ≠ b * a) {f₁ : D →* Y₁} {f₂ : D →* Y₂}
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (hsol : Group.IsSolvable ↥f₁.ker) : ∃ e : Y₁ ≃* Y₂, ∀ d : D, e (f₁ d) = f₂ d := by
  have hker := ker_eq_of_solvable hY₂ hf₁ hf₂ hsol
  set e₁ := QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁ with he₁
  set e₂ := QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂ with he₂
  refine ⟨(e₁.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)).trans e₂, fun d => ?_⟩
  have h1 : e₁.symm (f₁ d) = (d : D ⧸ f₁.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
