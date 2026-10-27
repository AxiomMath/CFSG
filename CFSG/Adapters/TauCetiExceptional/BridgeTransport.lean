module

public import CFSG.Adapters.TauCetiExceptional.BigCellEndgame
public import CFSG.Adapters.TauCetiExceptional.BigCellGeck

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell

variable {τ : Tag}

theorem natMat_entrywise {R : Type} [CommRing R] (σ : R →+* R)
    (A : Module.End R (RootModule τ R)) (i j : Fin (nLab τ)) :
    natMat τ R (entrywise σ A) i j = σ (natMat τ R A i j) := by
  rw [natMat_apply, natMat_apply, entrywise_single, Finsupp.mapRange_apply]

namespace GeckMatch

variable {t : DynkinType} {ht : t.Valid} (M : GeckMatch τ t ht)

theorem toGeck_symm_entrywise {A : Type} [CommRing A] (σ : A →+* A)
    (z z' : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A)
    (hz : ∀ r s, (z' : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      σ ((z : Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s)) :
    (M.toGeck A).symm z' = Units.map (entrywiseHom σ) ((M.toGeck A).symm z) := by
  refine Units.ext ((natMat τ A).injective (Matrix.ext fun i j => ?_))
  change natMat τ A ((M.toGeck A).symm z' : Module.End A (RootModule τ A)) i j =
    natMat τ A (entrywise σ ((M.toGeck A).symm z : Module.End A (RootModule τ A))) i j
  rw [natMat_entrywise, natMat_toGeck_symm_apply, natMat_toGeck_symm_apply, hz, map_mul, map_mul,
    map_intCast, map_intCast]

end GeckMatch

theorem map_baseChangeGL_adjointGroup_eq
    {K K' : Type} [Field K] [Field K'] (f : K ≃+* K') :
    (adjointGroup τ K).map (baseChangeGL (f : K →+* K')) = adjointGroup τ K' := by
  refine le_antisymm (map_baseChangeGL_adjointGroup_le _) ((Subgroup.closure_le _).2 ?_)
  rintro g ⟨i, c, hx | hy⟩
  · refine ⟨xUnit τ K i (f.symm c), xUnit_mem_adjointGroup _ _, ?_⟩
    rw [baseChangeGL_xUnit]
    refine Units.ext ?_
    rw [coe_xUnit, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact hx.symm
  · refine ⟨yUnit τ K i (f.symm c), yUnit_mem_adjointGroup _ _, ?_⟩
    rw [baseChangeGL_yUnit]
    refine Units.ext ?_
    rw [coe_yUnit, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact hy.symm

@[expose] def adjointGroupCongr
    {K K' : Type} [Field K] [Field K'] (f : K ≃+* K') :
    ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K') :=
  ((adjointGroup τ K).equivMapOfInjective _ (baseChangeGL_injective (f : K →+* K'))).trans
    (MulEquiv.subgroupCongr (map_baseChangeGL_adjointGroup_eq f))

@[expose] def adjointQuotientCongr
    {K K' : Type} [Field K] [Field K'] (f : K ≃+* K') :
    AdjointQuotient τ K ≃* AdjointQuotient τ K' :=
  QuotientGroup.congr _ _ (adjointGroupCongr f) (Subgroup.map_center_eq _)

@[expose] def derivedCentralQuotientEquiv
    {K L : Type} [Field K] [Field L] (f : K →+* L)
    (R : Subgroup (ModGL τ L)) (hR : ⁅R, R⁆ = (adjointGroup τ K).map (baseChangeGL f)) :
    TauCeti.DerivedCentralQuotient ↥R ≃* AdjointQuotient τ K := by
  have hmap : (commutator ↥R).map R.subtype = (adjointGroup τ K).map (baseChangeGL f) := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hR]
  exact QuotientGroup.congr _ _ ((((commutator ↥R).equivMapOfInjective R.subtype
    R.subtype_injective).trans (MulEquiv.subgroupCongr hmap)).trans
      ((adjointGroup τ K).equivMapOfInjective _ (baseChangeGL_injective f)).symm)
    (Subgroup.map_center_eq _)

end CFSG.TauCetiBridge
