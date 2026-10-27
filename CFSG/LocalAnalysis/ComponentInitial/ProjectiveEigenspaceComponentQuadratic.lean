module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CatalogueBProjectiveInvolution
  CatalogueBProjectiveCoordinates CatalogueBProjectiveQuadratic
open scoped MatrixGroups

namespace ProjectiveEigenspace

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

theorem three_le_card_of_two_ne_zero (htwo : (2 : K) ≠ 0) : 3 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h2 : Nat.card K ≠ 2 := by
    intro h
    apply htwo
    let : Fintype K := Fintype.ofFinite K
    have h3 := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, h] at h3
    exact_mod_cast h3
  omega

theorem eq_bot_of_isPerfect_of_le_centralizer_quadratic (htwo : (2 : K) ≠ 0) (hn : 2 ≤ n)
    {T : GL (Fin n) K} {μ : Kˣ} (hsq : T ^ 2 = GeneralLinearGroup.scalar (Fin n) μ)
    (hns : ¬ IsSquare μ.val) {L : Subgroup (centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (GL (Fin n) K)}
    (hR : R ≤ centralizer ((L.map (centralizer {T}).subtype : Subgroup (GL (Fin n) K)) :
      Set (GL (Fin n) K)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have : Fact (¬ IsSquare μ.val) := ⟨hns⟩
  let _ := matrixModule T μ hsq
  have : Finite (extension μ.val) := quadraticExtension_finite μ.val
  have : IsScalarTower K (extension μ.val) (Fin n → K) := matrixModule_scalarTower T μ hsq
  set m := matrixDimension T μ hsq with hm
  have hm1 : 1 ≤ m := matrixDimension_pos T μ hsq
  have hL' := isComponent_map_of_isComponent (matrixCentralizerQuadraticEquiv T μ hsq) hL
  set L' := L.map (matrixCentralizerQuadraticEquiv T μ hsq).toMonoidHom
  have : Group.IsPerfect L' := hL'.1.1
  have : Nontrivial L' := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  have hcardE : Nat.card (extension μ.val) = Nat.card K ^ 2 := by
    let : Fintype K := Fintype.ofFinite K
    let : Fintype (extension μ.val) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K),
      extension_finrank]
  have hK3 := three_le_card_of_two_ne_zero htwo
  have hE9 : 9 ≤ Nat.card (extension μ.val) := by
    rw [hcardE]
    nlinarith
  have hsmall : ¬ (m = 1 ∨ m = 2 ∧
      (Nat.card (extension μ.val) = 2 ∨ Nat.card (extension μ.val) = 3)) := by
    rintro (h1 | ⟨-, h2 | h2⟩)
    · have : Group.IsSolvable (GL (Fin m) (extension μ.val)) :=
        CatalogueBGeneralLinear.generalLinear_small_solvable m (extension μ.val) (Or.inl h1)
      exact Group.IsPerfect.not_isSolvable L' inferInstance
    · omega
    · omega
  obtain ⟨hm2, h22, h23⟩ :=
    CatalogueBGeneralLinear.retained_parameters m (extension μ.val) hm1 hsmall
  have hLeq := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m
    (extension μ.val) hm2 h22 h23 L' hL'.2
  let Ψ : ((Fin m → extension μ.val) × Unit) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.prodUnique.trans ((matrixBasis T μ hsq).equivFun.symm.restrictScalars K)
  have hΨ : ∀ v w, Ψ (v, w) = (matrixBasis T μ hsq).equivFun.symm v := fun v w => rfl
  have hS : ∀ s : SpecialLinearGroup (Fin m) (extension μ.val),
      ∃ g ∈ L.map (centralizer {T}).subtype, ∀ x,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ Ψ x =
          Ψ ((summandSL K (extension μ.val) Unit m s : _ →ₗ[K] _) x) := by
    intro s
    have hs : SpecialLinearGroup.toGL s ∈ L' := by
      rw [hLeq]
      exact ⟨s, rfl⟩
    obtain ⟨y, hy, hys⟩ := hs
    refine ⟨y, mem_map_of_mem _ hy, fun ⟨v, w⟩ => ?_⟩
    have h1 := matrixCentralizerQuadraticEquiv_mulVec T μ hsq y
      ((matrixBasis T μ hsq).equivFun.symm v)
    have hys' : matrixCentralizerQuadraticEquiv T μ hsq y = SpecialLinearGroup.toGL s := hys
    rw [hys', SpecialLinearGroup.coe_GL_coe_matrix, LinearEquiv.apply_symm_apply] at h1
    rw [summandSL_apply, hΨ, hΨ, h1, LinearEquiv.symm_apply_apply]
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply Units.ext
  rw [Units.val_one]
  refine matrix_eq_of_mulVec_eq fun x => ?_
  obtain ⟨⟨v, w⟩, rfl⟩ := Ψ.surjective x
  rw [one_mulVec]
  exact apply_eq_of_isPerfect_of_le_centralizer_transport hm2 Ψ hS hR hRp hg v

end ProjectiveEigenspace

end CFSG.LocalAnalysis.ComponentInitial
