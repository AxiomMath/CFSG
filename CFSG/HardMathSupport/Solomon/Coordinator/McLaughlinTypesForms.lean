module

public import CFSG.Open.StatedDefs
public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial

theorem mclt_zmod2_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  revert a
  decide

variable {V : Type*} [AddCommGroup V]

section Transport

variable {K : Type*} [Field K] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def mclt_glMatrixEquiv (b : Module.Basis ι K V) :
    LinearMap.GeneralLinearGroup K V ≃* GL ι K :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv

theorem mclt_glMatrixEquiv_mulVec (b : Module.Basis ι K V)
    (g : LinearMap.GeneralLinearGroup K V) (v : V) :
    ((mclt_glMatrixEquiv b g : GL ι K) : Matrix ι ι K).mulVec (b.equivFun v) =
      b.equivFun ((g : V →ₗ[K] V) v) := by
  simp only [Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (g : V →ₗ[K] V) v

theorem mclt_map_glMatrixEquiv_eq_closure (b : Module.Basis ι K V) {Q : V → K}
    {Q₀ : (ι → K) → K} (hQ : ∀ v, Q v = Q₀ (b.equivFun v))
    {G : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hG : ∀ g, g ∈ G ↔ ∀ v, Q ((g : V →ₗ[K] V) v) = Q v) :
    G.map (mclt_glMatrixEquiv b).toMonoidHom =
      Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K).mulVec v) = Q₀ v} := by
  have hA : ∀ (A : GL ι K) (v : V),
      b.equivFun ((((mclt_glMatrixEquiv b).symm A : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) v) = (A : Matrix ι ι K).mulVec (b.equivFun v) := by
    intro A v
    rw [← mclt_glMatrixEquiv_mulVec, MulEquiv.apply_symm_apply]
  have hset : {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K).mulVec v) = Q₀ v} =
      (G.map (mclt_glMatrixEquiv b).toMonoidHom : Set (GL ι K)) := by
    ext A
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_map_equiv, hG]
    constructor
    · intro h v
      rw [hQ, hQ, hA]
      exact h _
    · intro h w
      have := h (b.equivFun.symm w)
      rwa [hQ, hQ, hA, LinearEquiv.apply_symm_apply] at this
  rw [hset, Subgroup.closure_eq]

end Transport

theorem mclt_statedSL_eq_top (n : ℕ) : StatedSL n (ZMod 2) = ⊤ := by
  rw [StatedSL, eq_top_iff, ← Subgroup.closure_univ]
  refine Subgroup.closure_mono fun A _ => ?_
  change (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1
  exact mclt_zmod2_eq_one (Matrix.GeneralLinearGroup.det_ne_zero A)

noncomputable def mclt_glEquivStatedSL [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] :
    LinearMap.GeneralLinearGroup (ZMod 2) V ≃* StatedSL (finrank (ZMod 2) V) (ZMod 2) :=
  ((mclt_glMatrixEquiv (Module.finBasisOfFinrankEq (ZMod 2) V rfl)).trans
    Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr (mclt_statedSL_eq_top _).symm)

section Orthogonal

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Module K V]

theorem mclt_nonempty_equiv_orthGroup (b : Module.Basis ι K V) {Q : QuadraticForm K V}
    {Q₀ : (ι → K) → K} (hQ : ∀ v, Q v = Q₀ (b.equivFun v))
    {G : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hG : G = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom) :
    Nonempty (G ≃* GLAOrthGroup Q₀) := by
  have hmem : ∀ g, g ∈ G ↔ ∀ v, Q ((g : V →ₗ[K] V) v) = Q v := by
    intro g
    rw [hG, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  exact ⟨(G.equivMapOfInjective (mclt_glMatrixEquiv b).toMonoidHom
    (mclt_glMatrixEquiv b).injective).trans
      (MulEquiv.subgroupCongr (mclt_map_glMatrixEquiv_eq_closure b hQ hmem))⟩

variable [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem mclt_exists_basis_quadratic (Q : QuadraticForm (ZMod 2) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) :
    (∃ b : Module.Basis (Fin n ⊕ Fin n) (ZMod 2) V,
        ∀ v, Q v = GLAQPlus (ZMod 2) n (b.equivFun v)) ∨
      ∃ b : Module.Basis (GLAMinusIdx (n - 1)) (ZMod 2) V,
        ∀ v, Q v = GLAQMinus (n - 1) (1 : ZMod 2) 1 (b.equivFun v) := by
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    Q hQ).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, hβ, hroot, b, hb⟩
  · refine Or.inl ⟨b, fun v => ?_⟩
    have hv : v = ∑ i, b.repr v (.inl i) • b (.inl i) + ∑ i, b.repr v (.inr i) • b (.inr i) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Fintype.sum_sum_type]
    conv_lhs => rw [hv]
    rw [hb]
    rfl
  · obtain rfl : β = 1 := mclt_zmod2_eq_one hβ
    obtain rfl : γ = 1 := mclt_zmod2_eq_one fun h => hroot 0 (by rw [h]; ring)
    refine Or.inr ⟨b.reindex (Equiv.sumAssoc _ _ _).symm, fun v => ?_⟩
    have hv : v = ∑ i, b.repr v (.inl i) • b (.inl i) +
        ∑ i, b.repr v (.inr (.inl i)) • b (.inr (.inl i)) +
          b.repr v (.inr (.inr 0)) • b (.inr (.inr 0)) +
            b.repr v (.inr (.inr 1)) • b (.inr (.inr 1)) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
      abel
    conv_lhs => rw [hv]
    rw [hb]
    rfl

end Orthogonal

section Symplectic

noncomputable def mclt_bilinIsometryGroupEquiv {K : Type*} [Field K] [Module K V]
    (B : LinearMap.BilinForm K V) :
    bilinIsometryGroup B ≃* TauCeti.BilinForm.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).subgroupMap (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact TauCeti.BilinForm.mem_isometryGroup_iff.mpr hh
      · intro hg
        refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm g, ?_,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).apply_symm_apply g⟩
        exact TauCeti.BilinForm.mem_isometryGroup_iff.mp hg))

theorem mclt_exists_bilinIsometryGroup_equiv_statedSp {K : Type} [Field K] [Module K V]
    [FiniteDimensional K V] {f : LinearMap.BilinForm K V} (hnd : f.Nondegenerate)
    (halt : f.IsAlt) :
    ∃ m : ℕ, finrank K V = 2 * m ∧ Nonempty (bilinIsometryGroup f ≃* StatedSp m K) := by
  obtain ⟨m, b, hd, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis f halt hnd
  have hSp : TauCeti.GLSymplectic (Fin m) K = StatedSp m K :=
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm
  exact ⟨m, hd, ⟨((mclt_bilinIsometryGroupEquiv f).trans
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b f hb)).trans
      (MulEquiv.subgroupCongr hSp)⟩⟩

end Symplectic

end CFSG.HardMathSupport.Solomon.Coordinator
