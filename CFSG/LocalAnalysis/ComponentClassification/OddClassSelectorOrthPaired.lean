module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth_paired_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) (b : Kˣ)
    (hb : (d : K) = (b : K) ^ 2) (hμ : (μ : K) / (d : K) = -1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  obtain ⟨hc, -, -, -, hneg⟩ := hsq b hb
  obtain ⟨-, -, -, hdimeq, -, -, E, -, -, -, -, -⟩ := hneg hμ
  obtain ⟨m, hm⟩ : ∃ m, finrank K (positiveSquareKernel A b) = m := ⟨_, rfl⟩
  have hdimV : m + m = finrank K V := by
    rw [← Submodule.finrank_add_eq_of_isCompl hc, ← hdimeq, hm]
  have hm4 : 4 ≤ m := by omega
  obtain ⟨bP⟩ : Nonempty (Basis (Fin m) K (positiveSquareKernel A b)) :=
    ⟨Module.finBasisOfFinrankEq K _ hm⟩
  set F : orthogonalOperatorCentralizer Q A.toLinearMap ≃* Matrix.GeneralLinearGroup (Fin m) K :=
    E.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)) with hF
  have hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hY.1.trans inf_le_left
  have hY₂ : CFSG.Assembly.IsComponentOf (Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
      (orthogonalOperatorCentralizer Q A.toLinearMap) := by
    have h := isComponentOf_comap_of_le_range (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective hY
      (by rw [Subgroup.range_subtype]; exact inf_le_left)
    have hC : (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap).comap
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
          orthogonalOperatorCentralizer Q A.toLinearMap := by
      rw [Subgroup.comap_inf]
      have hOO : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = ⊤ :=
        Subgroup.subgroupOf_self (TauCeti.QuadraticMap.orthogonalGroup Q)
      rw [hOO, top_inf_eq]
      rfl
    rwa [hC] at h
  have hY₁ : CFSG.IsComponent
      ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hY₂.1).mp hY₂
  set eY : ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap)) ≃* Y :=
    (Subgroup.subgroupOfEquivOfLe hY₂.1).trans (Subgroup.subgroupOfEquivOfLe hYO) with heY
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent F hY₁
  have : Group.IsPerfect ((((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap))).map F.toMonoidHom) := hL'.1.1
  have : Nontrivial ((((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap))).map F.toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  have hSL : (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap))).map F.toMonoidHom =
        CatalogueBGeneralLinear.specialLinearRange m K := by
    obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters m K (by omega)
      (by omega)
    exact CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m K hm2 h22 h23 _ hL'.2
  have hmem : ∀ M : Matrix.SpecialLinearGroup (Fin m) K,
      F.symm (Matrix.SpecialLinearGroup.toGL M) ∈
        ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
          (orthogonalOperatorCentralizer Q A.toLinearMap)) := by
    intro M
    have h1 : Matrix.SpecialLinearGroup.toGL M ∈
        (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
          (orthogonalOperatorCentralizer Q A.toLinearMap))).map F.toMonoidHom := by
      rw [hSL]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := h1
    rw [← hxM]
    simpa using hx
  set ψ : Matrix.SpecialLinearGroup (Fin m) K →* Y :=
    eY.toMonoidHom.comp ((F.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL).codRestrict _
      hmem) with hψ
  have hψi : Function.Injective ψ := by
    intro x y hxy
    have h1 := congrArg Subtype.val (eY.injective hxy)
    exact Matrix.SpecialLinearGroup.toGL_injective (F.symm.injective h1)
  exact false_of_smallSource hs (OddSelector.not_small_source_of_sl_cover (by omega) hℓ hℓ2 he
    hK (σ.comp ψ) (ker_comp_le_center ψ hψi σ hσk))

end CFSG.ComponentClassification.OddClassSelector
