module

public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open scoped Matrix
open Module

private lemma equivFun_smul_of_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (b : Basis ι F V) (h : SpecialLinearGroup F V) (w : V) :
    b.equivFun (h w) =
      (((Matrix.SpecialLinearGroup.toLin_equiv b).symm h : Matrix.SpecialLinearGroup ι F) :
        Matrix ι ι F) *ᵥ b.equivFun w := by
  have hm : (((Matrix.SpecialLinearGroup.toLin_equiv b).symm h :
      Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) =
      LinearMap.toMatrix b b (h : V →ₗ[F] V) :=
    Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b h
  rw [hm, Basis.equivFun_apply b w,
    LinearMap.toMatrix_mulVec_repr b b (h : V →ₗ[F] V) w, Basis.equivFun_apply b (h w)]
  rfl

private lemma comp_smul {ι : Type*} {F : Type*} [Field F]
    (σ : F ≃+* F) (c : F) (x : ι → F) :
    σ ∘ (c • x) = σ c • (σ ∘ x) := by
  ext i
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul]

private lemma mulVec_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]
    (A : GL ι F) (Q : Matrix ι ι F) (y : ι → F) :
    ((A : Matrix ι ι F) * Q * ((A⁻¹ : GL ι F) : Matrix ι ι F)) *ᵥ
        ((A : Matrix ι ι F) *ᵥ y) = (A : Matrix ι ι F) *ᵥ (Q *ᵥ y) := by
  have hAA : ((A⁻¹ : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul]
    exact A.inv_mul
  calc ((A : Matrix ι ι F) * Q * ((A⁻¹ : GL ι F) : Matrix ι ι F)) *ᵥ
        ((A : Matrix ι ι F) *ᵥ y)
      = ((A : Matrix ι ι F) * Q) *ᵥ
          (((A⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ ((A : Matrix ι ι F) *ᵥ y)) :=
        (Matrix.mulVec_mulVec ((A : Matrix ι ι F) *ᵥ y)
          ((A : Matrix ι ι F) * Q) ((A⁻¹ : GL ι F) : Matrix ι ι F)).symm
    _ = ((A : Matrix ι ι F) * Q) *ᵥ
          ((((A⁻¹ : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F)) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec y ((A⁻¹ : GL ι F) : Matrix ι ι F)
          (A : Matrix ι ι F)]
    _ = ((A : Matrix ι ι F) * Q) *ᵥ (1 *ᵥ y) := by rw [hAA]
    _ = ((A : Matrix ι ι F) * Q) *ᵥ y := by rw [Matrix.one_mulVec]
    _ = (A : Matrix ι ι F) *ᵥ (Q *ᵥ y) :=
        (Matrix.mulVec_mulVec y (A : Matrix ι ι F) Q).symm

private lemma map_mulVec_of_ringEquiv {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (σ : F ≃+* F) (M : Matrix ι ι F) (v : ι → F) :
    M.map σ *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec (σ : F →+* F) M v i).symm

private lemma dualBasis_equivFun_transpose
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (b : Basis ι F V) (u : V ≃ₗ[F] V) (f : Module.Dual F V) :
    b.dualBasis.equivFun (f ∘ₗ u.toLinearMap) =
      (LinearMap.toMatrix b b u.toLinearMap)ᵀ *ᵥ b.dualBasis.equivFun f := by
  rw [← Module.Dual.transpose_apply u.toLinearMap f,
    Basis.equivFun_apply b.dualBasis (Module.Dual.transpose (R := F) u.toLinearMap f),
    ← LinearMap.toMatrix_mulVec_repr b.dualBasis b.dualBasis
      (Module.Dual.transpose (R := F) u.toLinearMap) f,
    LinearMap.toMatrix_transpose, Basis.equivFun_apply b.dualBasis f]

theorem exists_semilinear_form_of_mulAut_sl {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (hV : 3 ≤ Module.finrank F V)
    (α : MulAut (SpecialLinearGroup F V)) :
    ∃ σ : F ≃+* F,
      (∃ T : V ≃+ V, (∀ (c : F) (v : V), T (c • v) = σ c • T v) ∧
        ∀ (g : SpecialLinearGroup F V) (v : V), α g (T v) = T (g v)) ∨
      (∃ T : Module.Dual F V ≃+ V,
        (∀ (c : F) (f : Module.Dual F V), T (c • f) = σ c • T f) ∧
        ∀ (g : SpecialLinearGroup F V) (f : Module.Dual F V),
          α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) := by
  classical
  let n := Module.finrank F V
  let b : Basis (Fin n) F V := Module.finBasis F V
  have hn : 3 ≤ n := hV
  let e : SpecialLinearGroup F V ≃* Matrix.SpecialLinearGroup (Fin n) F :=
    (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  let β : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := MulAut.congr e α
  have hcongr : ∀ h : SpecialLinearGroup F V, e (α h) = β (e h) := fun h => by
    simp [β, MulAut.congr, MulEquiv.trans_apply]
  obtain ⟨A, σ, hA⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hn β
  let σa : (Fin n → F) ≃+ (Fin n → F) :=
    AddEquiv.piCongrRight (fun _ : Fin n => σ.toAddEquiv)
  let Aaₗ : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    { toFun := fun x => (A : Matrix (Fin n) (Fin n) F) *ᵥ x
      invFun := fun x => ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x
      left_inv := fun x => by
        have hAA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (A : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul]
          exact A.inv_mul
        change ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
      right_inv := fun x => by
        have hAA : (A : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
          rw [← Units.val_mul]
          exact A.mul_inv
        change (A : Matrix (Fin n) (Fin n) F) *ᵥ
          (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
      map_add' := fun x y => Matrix.mulVec_add _ x y
      map_smul' := fun c x => Matrix.mulVec_smul _ c x }
  let Aa : (Fin n → F) ≃+ (Fin n → F) := Aaₗ.toAddEquiv
  have hσa_apply : ∀ x : Fin n → F, σa x = σ ∘ x := fun x => rfl
  have hAa_apply : ∀ x : Fin n → F,
      Aa x = (A : Matrix (Fin n) (Fin n) F) *ᵥ x := fun x => rfl
  rcases hA with hA | hA
  ·
    let T : V ≃+ V :=
      (b.equivFun : V ≃+ (Fin n → F)).trans
        (σa.trans (Aa.trans (b.equivFun.symm : (Fin n → F) ≃+ V)))
    have hT : ∀ v : V,
        T v = b.equivFun.symm ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.equivFun v)) := by
      intro v
      change b.equivFun.symm (Aa (σa (b.equivFun v))) =
        b.equivFun.symm ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.equivFun v))
      rw [hAa_apply, hσa_apply]
    refine ⟨σ, Or.inl ⟨T, ?_, ?_⟩⟩
    · intro c v
      rw [hT (c • v), hT v, map_smul b.equivFun c v,
        comp_smul σ c (b.equivFun v),
        Matrix.mulVec_smul (A : Matrix (Fin n) (Fin n) F) (σ c) (σ ∘ b.equivFun v),
        map_smul b.equivFun.symm (σ c)
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.equivFun v))]
    · intro g v
      have hR : b.equivFun (T (g v)) =
          (A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘
            ((e g : Matrix (Fin n) (Fin n) F) *ᵥ b.equivFun v)) := by
        rw [hT (g v), LinearEquiv.apply_symm_apply, equivFun_smul_of_matrix b g v]
      have hL : b.equivFun (α g (T v)) =
          (A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘
            ((e g : Matrix (Fin n) (Fin n) F) *ᵥ b.equivFun v)) := by
        rw [equivFun_smul_of_matrix b (α g) (T v), hT v, LinearEquiv.apply_symm_apply,
          hcongr g, hA (e g), mulVec_conj, map_mulVec_of_ringEquiv]
      exact b.equivFun.injective (hL.trans hR.symm)
  ·
    let T : Module.Dual F V ≃+ V :=
      (b.dualBasis.equivFun : Module.Dual F V ≃+ (Fin n → F)).trans
        (σa.trans (Aa.trans (b.equivFun.symm : (Fin n → F) ≃+ V)))
    have hT : ∀ f : Module.Dual F V,
        T f = b.equivFun.symm
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.dualBasis.equivFun f)) := by
      intro f
      change b.equivFun.symm (Aa (σa (b.dualBasis.equivFun f))) =
        b.equivFun.symm ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.dualBasis.equivFun f))
      rw [hAa_apply, hσa_apply]
    refine ⟨σ, Or.inr ⟨T, ?_, ?_⟩⟩
    · intro c f
      rw [hT (c • f), hT f, map_smul b.dualBasis.equivFun c f,
        comp_smul σ c (b.dualBasis.equivFun f),
        Matrix.mulVec_smul (A : Matrix (Fin n) (Fin n) F) (σ c)
          (σ ∘ b.dualBasis.equivFun f),
        map_smul b.equivFun.symm (σ c)
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘ b.dualBasis.equivFun f))]
    · intro g f
      let M : Matrix (Fin n) (Fin n) F :=
        ((e g)⁻¹ : Matrix.SpecialLinearGroup (Fin n) F)
      have hM : (LinearMap.toMatrix b b
            (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) = M := by
        change LinearMap.toMatrix b b
          ((g⁻¹ : SpecialLinearGroup F V) : V →ₗ[F] V) = M
        rw [← Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b (g⁻¹)]
        exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) F =>
          (z : Matrix (Fin n) (Fin n) F)) (MulEquiv.map_inv e g)
      have hdual : b.dualBasis.equivFun
            (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) =
          M.transpose *ᵥ b.dualBasis.equivFun f := by
        rw [dualBasis_equivFun_transpose b (SpecialLinearGroup.toLinearEquiv g⁻¹) f, hM]
      have hR : b.equivFun
            (T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) =
          (A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘
            (M.transpose *ᵥ b.dualBasis.equivFun f)) := by
        rw [hT, LinearEquiv.apply_symm_apply, hdual]
      have hL : b.equivFun (α g (T f)) =
          (A : Matrix (Fin n) (Fin n) F) *ᵥ (σ ∘
            (M.transpose *ᵥ b.dualBasis.equivFun f)) := by
        rw [equivFun_smul_of_matrix b (α g) (T f), hT f, LinearEquiv.apply_symm_apply,
          hcongr g, hA (e g), mulVec_conj, map_mulVec_of_ringEquiv]
      exact b.equivFun.injective (hL.trans hR.symm)

end CFSG.LinearAlgebra.RootGroupSL
