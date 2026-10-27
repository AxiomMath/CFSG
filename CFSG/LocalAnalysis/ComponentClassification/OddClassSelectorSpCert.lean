module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSp
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSL

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)

theorem eq_top_of_isComponent_of_quasisimple {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G)
    {Y : Subgroup G} (hY : CFSG.IsComponent Y) : Y = ⊤ := by
  have : Group.IsPerfect Y := hY.1.1
  have : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hY.1
  exact (Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    (CatalogueBAlternating.quasisimple_iff_native.mp hG) Y
    (Components.chain_of_mathlib_subnormal hY.2)).resolve_left
      (Y.nontrivial_iff_ne_bot.mp inferInstance)

variable {k : Type} [Field k] [Finite k]

theorem sp_component_false {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j)
    (B : BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate) (hdim : 4 ≤ finrank k W)
    {H : Type*} [Group H] (F : H ≃* CatalogueBAlternatingIsometry.isometryGroup B)
    {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hq := CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le B hB hnd hdim hodd
  have hYtop := eq_top_of_isComponent_of_quasisimple hq
    (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent F hY)
  obtain ⟨m, hd, ⟨eSp⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := k)
  let τ : CFSG.Assembly.LowTwoRank.StatedSp m k ≃* Y :=
    (((MulEquiv.subgroupCongr heq).trans eSp.symm).trans
      ((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv).symm).trans
        (Y.equivMapOfInjective F.toMonoidHom F.injective).symm
  exact false_of_smallSource hs (OddSelector.not_small_source_of_sp_cover (r := m) (by omega)
    hℓ hℓ2 hj hk (σ.comp τ.toMonoidHom) (ker_comp_le_center τ.toMonoidHom τ.injective σ hσk))

theorem gl_component_false {m ℓ j : ℕ} (hm : 3 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = ℓ ^ j) {H : Type*} [Group H]
    (F : H ≃* Matrix.GeneralLinearGroup (Fin m) k) {Y : Subgroup H} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent F hY
  have : Group.IsPerfect (Y.map F.toMonoidHom) := hL'.1.1
  have : Nontrivial (Y.map F.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  have hSL : Y.map F.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange m k := by
    obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters m k (by omega)
      (by omega)
    exact CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m k hm2 h22 h23 _ hL'.2
  have hmem : ∀ M : Matrix.SpecialLinearGroup (Fin m) k,
      F.symm (Matrix.SpecialLinearGroup.toGL M) ∈ Y := by
    intro M
    have h1 : Matrix.SpecialLinearGroup.toGL M ∈ Y.map F.toMonoidHom := by
      rw [hSL]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := h1
    rw [← hxM]
    simpa using hx
  let ψ : Matrix.SpecialLinearGroup (Fin m) k →* Y :=
    (F.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL).codRestrict _ hmem
  have hψi : Function.Injective ψ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Matrix.SpecialLinearGroup.toGL_injective (F.symm.injective h1)
  exact false_of_smallSource hs (OddSelector.not_small_source_of_sl_cover hm hℓ hℓ2 hj hk
    (σ.comp ψ) (ker_comp_le_center ψ hψi σ hσk))

end CFSG.ComponentClassification.OddClassSelector
