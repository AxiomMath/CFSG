module

public import CFSG.Adapters.TauCetiExceptional.Interface
public import CFSG.Blueprint.ChevalleyWeyl

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint.Chevalley TauCeti

@[expose] def geckElementary (t : DynkinType) (ht : t.Valid) (A : Type) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :=
  Subgroup.closure {g | ∃ (j : Fin t.rank ⊕ Fin t.rank) (u : Multiplicative A),
    g = (t.geckRootSubgroupPoints ht j A u : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)}

theorem geckElementary_le_geckPoints (t : DynkinType) (ht : t.Valid) (A : Type) [CommRing A] :
    geckElementary t ht A ≤ t.geckPoints ht A := by
  rw [geckElementary, Subgroup.closure_le]
  rintro _ ⟨j, u, rfl⟩
  exact (t.geckRootSubgroupPoints ht j A u).2

namespace GeckMatch

variable {τ : Tag} {t : DynkinType} {ht : t.Valid} (M : GeckMatch τ t ht)
variable (A : Type) [CommRing A]

@[expose] def unitSign (s : Fin (t.geckDim ht)) : Aˣ :=
  Units.map (Int.castRingHom A).toMonoidHom (M.sgn s)

theorem coe_unitSign (s : Fin (t.geckDim ht)) : (M.unitSign A s : A) = ((M.sgn s : ℤ) : A) :=
  rfl

theorem coe_unitSign_inv (s : Fin (t.geckDim ht)) :
    (((M.unitSign A s)⁻¹ : Aˣ) : A) = ((M.sgn s : ℤ) : A) := by
  rw [unitSign, ← map_inv, Int.units_inv_eq_self]
  rfl

@[expose] def geckBasis : Module.Basis (Fin (t.geckDim ht)) A (RootModule τ A) :=
  (Finsupp.basisSingleOne.reindex M.lab.symm).unitsSMul (M.unitSign A)

@[expose] def toGeck :
    (Module.End A (RootModule τ A))ˣ ≃* Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv (M.geckBasis A)).toMulEquiv

theorem toGeck_apply (g : (Module.End A (RootModule τ A))ˣ) (r s : Fin (t.geckDim ht)) :
    ((M.toGeck A g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      ((M.sgn r : ℤ) : A) * (g : Module.End A (RootModule τ A))
        (Finsupp.single (M.lab s) (1 : A)) (M.lab r) * ((M.sgn s : ℤ) : A) := by
  simp only [toGeck, Units.coe_mapEquiv, MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, LinearMap.toMatrixAlgEquiv_apply, geckBasis, Module.Basis.repr_unitsSMul,
    Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
    Equiv.symm_symm, map_smul, Finsupp.smul_apply, Units.smul_def, smul_eq_mul,
    coe_unitSign_inv, coe_unitSign]
  ring

theorem toGeck_xUnit
    (i : Fin t.rank) (c : A) :
    M.toGeck A (xUnit τ A (M.node i) c) =
      (t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  ext r s
  rw [toGeck_apply, M.matrix_inl]
  rfl

theorem toGeck_yUnit
    (i : Fin t.rank) (c : A) :
    M.toGeck A (yUnit τ A (M.node i) c) =
      (t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  ext r s
  rw [toGeck_apply, M.matrix_inr]
  rfl

theorem map_toGeck_adjointGroup
    (K : Type) [Field K] :
    (adjointGroup τ K).map (M.toGeck K).toMonoidHom = geckElementary t ht K := by
  rw [adjointGroup, MonoidHom.map_closure, geckElementary]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨i, c, hx | hx⟩, rfl⟩
    · have hxe : x = xUnit τ K (M.node (M.node.symm i)) c := by
        rw [Equiv.apply_symm_apply]
        exact Units.ext hx
      refine ⟨.inl (M.node.symm i), Multiplicative.ofAdd c, ?_⟩
      rw [hxe]
      exact M.toGeck_xUnit K _ c
    · have hxe : x = yUnit τ K (M.node (M.node.symm i)) c := by
        rw [Equiv.apply_symm_apply]
        exact Units.ext hx
      refine ⟨.inr (M.node.symm i), Multiplicative.ofAdd c, ?_⟩
      rw [hxe]
      exact M.toGeck_yUnit K _ c
  · rintro ⟨j | j, u, rfl⟩
    · exact ⟨xUnit τ K (M.node j) (Multiplicative.toAdd u),
        ⟨M.node j, Multiplicative.toAdd u, Or.inl rfl⟩, M.toGeck_xUnit K j _⟩
    · exact ⟨yUnit τ K (M.node j) (Multiplicative.toAdd u),
        ⟨M.node j, Multiplicative.toAdd u, Or.inr rfl⟩, M.toGeck_yUnit K j _⟩

theorem map_toGeck_adjointGroup_le_geckPoints
    (K : Type) [Field K] :
    (adjointGroup τ K).map (M.toGeck K).toMonoidHom ≤ t.geckPoints ht K := by
  rw [map_toGeck_adjointGroup]
  exact geckElementary_le_geckPoints t ht K

end GeckMatch

end CFSG.TauCetiBridge
