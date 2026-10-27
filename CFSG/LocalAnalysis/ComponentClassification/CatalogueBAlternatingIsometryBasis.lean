module

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBAlternatingIsometry

open LinearMap (BilinForm)
open scoped Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev isometryGroup (B : BilinForm K V) : Subgroup (V ≃ₗ[K] V) :=
  TauCeti.BilinForm.isometryGroup B

theorem mem_isometryGroup_iff (B : BilinForm K V) (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup B ↔ ∀ x y, B (g x) (g y) = B x y :=
  TauCeti.BilinForm.mem_isometryGroup_iff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def basisMatrixEquiv (b : Module.Basis ι K V) :
    (V ≃ₗ[K] V) ≃* Matrix.GeneralLinearGroup ι K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem basisMatrixEquiv_val (b : Module.Basis ι K V) (g : V ≃ₗ[K] V) :
    (basisMatrixEquiv b g).val = LinearMap.toMatrix b b g.toLinearMap := rfl

theorem basisMatrixEquiv_mulVec (b : Module.Basis ι K V) (g : V ≃ₗ[K] V) (v : V) :
    (basisMatrixEquiv b g).val.mulVec (b.equivFun v) = b.equivFun (g v) := by
  rw [basisMatrixEquiv_val]
  exact LinearMap.toMatrix_mulVec_repr b b g.toLinearMap v

theorem isometry_iff_matrix (b : Module.Basis ι K V) (B : BilinForm K V)
    (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup B ↔
      (basisMatrixEquiv b g).valᵀ * BilinForm.toMatrix b B *
        (basisMatrixEquiv b g).val = BilinForm.toMatrix b B := by
  rw [basisMatrixEquiv_val]
  rw [TauCeti.BilinForm.mem_isometryGroup]
  exact TauCeti.BilinForm.isIsometry_iff_toMatrix b

theorem isometry_iff_symplectic {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) K V)
    (B : BilinForm K V) (hb : BilinForm.toMatrix b B = Matrix.J (Fin m) K)
    (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup B ↔ basisMatrixEquiv b g ∈ TauCeti.GLSymplectic (Fin m) K := by
  rw [isometry_iff_matrix b B g, hb, TauCeti.GLSymplectic.mem_iff']

@[expose] def isometryMatrixEquiv {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) K V)
    (B : BilinForm K V) (hb : BilinForm.toMatrix b B = Matrix.J (Fin m) K) :
    isometryGroup B ≃* TauCeti.GLSymplectic (Fin m) K where
  toFun g := ⟨basisMatrixEquiv b g.val, (isometry_iff_symplectic b B hb g.val).mp g.property⟩
  invFun A := ⟨(basisMatrixEquiv b).symm A.val,
    (isometry_iff_symplectic b B hb _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact A.property)⟩
  left_inv g := Subtype.ext ((basisMatrixEquiv b).symm_apply_apply g.val)
  right_inv A := Subtype.ext ((basisMatrixEquiv b).apply_symm_apply A.val)
  map_mul' g h := Subtype.ext ((basisMatrixEquiv b).map_mul g.val h.val)

theorem isometryMatrixEquiv_val {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) K V)
    (B : BilinForm K V) (hb : BilinForm.toMatrix b B = Matrix.J (Fin m) K)
    (g : isometryGroup B) :
    (isometryMatrixEquiv b B hb g).val = basisMatrixEquiv b g.val := rfl

theorem isometryMatrixEquiv_symm_mulVec {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) K V) (B : BilinForm K V)
    (hb : BilinForm.toMatrix b B = Matrix.J (Fin m) K)
    (A : TauCeti.GLSymplectic (Fin m) K) (v : V) :
    A.val.val.mulVec (b.equivFun v) =
      b.equivFun (((isometryMatrixEquiv b B hb).symm A).val v) := by
  change A.val.val.mulVec (b.equivFun v) =
    b.equivFun (((basisMatrixEquiv b).symm A.val) v)
  simpa using basisMatrixEquiv_mulVec b ((basisMatrixEquiv b).symm A.val) v

variable [FiniteDimensional K V]

theorem exists_symplectic_basis (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) K V),
      Module.finrank K V = 2 * m ∧ BilinForm.toMatrix b B = Matrix.J (Fin m) K := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  refine ⟨m, b, ?_, hb⟩
  rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, two_mul]

theorem even_finrank (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank K V) := hB.even_finrank hnd

theorem exists_blueprint_symplectic_basis (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) K V),
      Module.finrank K V = 2 * m ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      (∀ i j, B (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) := by
  obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis B hB hnd
  refine ⟨m, b.reindex (Equiv.sumComm _ _), hd, ?_, ?_, ?_⟩
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using congrFun₂ hb (Sum.inr i) (Sum.inr j)
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using congrFun₂ hb (Sum.inl i) (Sum.inl j)
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using congrFun₂ hb (Sum.inr i) (Sum.inl j)

theorem exists_isometryEquiv_symplectic (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) :
    ∃ m : ℕ, Module.finrank K V = 2 * m ∧
      Nonempty (isometryGroup B ≃* TauCeti.GLSymplectic (Fin m) K) := by
  obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis B hB hnd
  exact ⟨m, hd, ⟨isometryMatrixEquiv b B hb⟩⟩

theorem exists_form_isometry {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (B : BilinForm K V) (C : BilinForm K W)
    (hB : B.IsAlt) (hBnd : B.Nondegenerate) (hC : C.IsAlt) (hCnd : C.Nondegenerate)
    (hd : Module.finrank K V = Module.finrank K W) : Nonempty (B.IsometryEquiv C) := by
  obtain ⟨m, b, hm, hb⟩ := exists_symplectic_basis B hB hBnd
  obtain ⟨n, c, hn, hc⟩ := exists_symplectic_basis C hC hCnd
  have hmn : m = n := by omega
  subst n
  exact ⟨b.isometryEquivOfToMatrixEq c (hb.trans hc.symm)⟩

theorem exists_symplectic_basis_prescribed_pair (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (a b : V) (hab : B a b = 1) :
    ∃ (m : ℕ) (c : Module.Basis (Fin (m + 1) ⊕ Fin (m + 1)) K V),
      Module.finrank K V = 2 * (m + 1) ∧
      (∀ i j, B (c (Sum.inl i)) (c (Sum.inl j)) = 0) ∧
      (∀ i j, B (c (Sum.inr i)) (c (Sum.inr j)) = 0) ∧
      (∀ i j, B (c (Sum.inl i)) (c (Sum.inr j)) = if i = j then 1 else 0) ∧
      c (Sum.inl 0) = a ∧ c (Sum.inr 0) = b := by
  let U := B.orthogonal (Submodule.span K {b, a})
  have halt : (B.restrict U).IsAlt := fun x => hB.self_eq_zero x
  have hUnd : (B.restrict U).Nondegenerate :=
    hB.restrict_nondegenerate_orthogonal_span_pair hab hnd
  obtain ⟨m, c, hc⟩ := halt.exists_basis_toMatrix_eq_J hUnd
  have hc' : ∀ x y, B (c x) (c y) = Matrix.J (Fin m) K x y := fun x y => by
    rw [← hc, BilinForm.toMatrix_apply, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  obtain ⟨d, hd, hfun⟩ :=
    hB.exists_basis_apply_eq_J_of_basis_orthogonal_span_pair hnd hab c hc'
  refine ⟨m, d.reindex (Equiv.sumComm _ _), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis d, Fintype.card_sum, Fintype.card_fin, two_mul]
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using hd (Sum.inr i) (Sum.inr j)
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using hd (Sum.inl i) (Sum.inl j)
  · intro i j
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
      using hd (Sum.inr i) (Sum.inl j)
  · simp [Module.Basis.reindex_apply, hfun]
  · simp [Module.Basis.reindex_apply, hfun]

end CFSG.ComponentClassification.CatalogueBAlternatingIsometry
