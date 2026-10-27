module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic SemidirectProduct
  CFSG.Sporadic.Recognition.HSMultiplier

theorem map_center_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (centerCongr e ⟨y, hy⟩).2
  · intro x hx
    exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).2, e.apply_symm_apply x⟩

section Hmod


theorem mul_ofAdd_one_self (a : Multiplicative (ZMod 2)) (ha : a ≠ 1) : a * a = 1 := by
  revert a
  decide

@[expose] noncomputable def HSCtx.sigmaHom (hΛ : HSCtx) :
    Multiplicative (ZMod 2) →* MulAut HSCover where
  toFun a := if a = 1 then 1 else hΛ.sigmaAut
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 1
    · simp [ha]
    · by_cases hb : b = 1
      · simp [hb]
      · have hab : a * b = 1 := by
          have h2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
          exact h2 a b ha hb
        simp only [ha, hb, hab, ite_true, ite_false]
        ext x
        exact (hΛ.sigma_sigma x).symm

abbrev HSCtx.Hmod (hΛ : HSCtx) : Type := HSCover ⋊[hΛ.sigmaHom] Multiplicative (ZMod 2)

@[expose] noncomputable def HSCtx.Emod (hΛ : HSCtx) : Subgroup hΛ.Hmod :=
  (inl : HSCover →* hΛ.Hmod).range

@[expose] def one2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem one2_ne_one : one2 ≠ 1 := by decide

theorem one2_mul_self : one2 * one2 = 1 := mul_ofAdd_one_self _ one2_ne_one

@[expose] noncomputable def HSCtx.yMod (hΛ : HSCtx) : hΛ.Hmod := inr one2

theorem HSCtx.sigmaHom_one2 (hΛ : HSCtx) : hΛ.sigmaHom one2 = hΛ.sigmaAut := by
  simp [HSCtx.sigmaHom, one2_ne_one]

theorem HSCtx.yMod_conj (hΛ : HSCtx) (x : HSCover) :
    hΛ.yMod * inl x * hΛ.yMod⁻¹ = inl (hΛ.sigma x) := by
  have := inl_aut (φ := hΛ.sigmaHom) one2 x
  rw [hΛ.sigmaHom_one2] at this
  exact this.symm

theorem HSCtx.yMod_mul_self (hΛ : HSCtx) : hΛ.yMod * hΛ.yMod = 1 := by
  rw [HSCtx.yMod, ← map_mul, one2_mul_self, map_one]

theorem HSCtx.mem_Emod_iff (hΛ : HSCtx) (x : hΛ.Hmod) : x ∈ hΛ.Emod ↔ x.right = 1 := by
  rw [HSCtx.Emod, range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  rfl

theorem HSCtx.yMod_not_mem (hΛ : HSCtx) : hΛ.yMod ∉ hΛ.Emod := by
  rw [hΛ.mem_Emod_iff]
  exact one2_ne_one

theorem HSCtx.Emod_normal (hΛ : HSCtx) : hΛ.Emod.Normal := by
  rw [HSCtx.Emod, range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

theorem HSCtx.Emod_index (hΛ : HSCtx) : hΛ.Emod.index = 2 := by
  rw [HSCtx.Emod, range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 rightHom_surjective, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

@[expose] noncomputable def HSCtx.eEmod (hΛ : HSCtx) : HSCover ≃* hΛ.Emod :=
  MonoidHom.ofInjective (inl_injective (φ := hΛ.sigmaHom))

theorem HSCtx.centralizer_Emod_le (hΛ : HSCtx) :
    centralizer (hΛ.Emod : Set hΛ.Hmod) ≤ hΛ.Emod := by
  intro x hx
  by_contra hxE
  have hr : x.right ≠ 1 := fun h => hxE ((hΛ.mem_Emod_iff x).2 h)
  apply hΛ.sigma_not_inner
  refine ⟨x.left⁻¹, fun z => ?_⟩
  have hz : x * inl z = inl z * x := by
    have := mem_centralizer_iff.1 hx (inl z) ⟨z, rfl⟩
    exact this.symm
  have h1 := congrArg SemidirectProduct.left hz
  have hφ : hΛ.sigmaHom x.right = hΛ.sigmaAut := by simp [HSCtx.sigmaHom, hr]
  simp only [SemidirectProduct.mul_left, left_inl, right_inl, map_one, MulAut.one_apply] at h1
  rw [hφ] at h1
  have h2 : hΛ.sigmaAut z = hΛ.sigma z := rfl
  rw [h2] at h1
  calc hΛ.sigma z = x.left⁻¹ * (x.left * hΛ.sigma z) := by group
    _ = x.left⁻¹ * (z * x.left) := by rw [h1]
    _ = x.left⁻¹ * z * x.left⁻¹⁻¹ := by group

theorem HSCtx.isHSCover (hΛ : HSCtx) : IsHSCover hΛ.Hmod hΛ.Emod where
  normal := hΛ.Emod_normal
  index_dvd_two := by rw [hΛ.Emod_index]
  perfect := by
    have := hΛ.perfect
    exact Group.IsPerfect.ofSurjective (f := hΛ.eEmod.toMonoidHom) hΛ.eEmod.surjective
  card_center := by
    rw [← Nat.card_congr (centerCongr hΛ.eEmod).toEquiv]
    exact hΛ.card_center
  quotient := by
    obtain ⟨e⟩ := hΛ.quotient
    exact ⟨(QuotientGroup.congr (center HSCover) (center hΛ.Emod) hΛ.eEmod
      (map_center_eq_of_mulEquiv hΛ.eEmod)).symm.trans e⟩
  centralizer_le := hΛ.centralizer_Emod_le

end Hmod

end CFSG.EvenSporadicStandard.TwoHS
