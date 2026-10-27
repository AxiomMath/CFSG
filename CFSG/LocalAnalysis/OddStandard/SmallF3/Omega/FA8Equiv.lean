module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem fa8_scalarSigns_eq_piGroup : scalarSigns Q = piGroup Q := by
  ext g
  rw [mem_scalarSigns_iff, mem_piGroup_iff]
  rfl

@[expose] noncomputable def fa8ClassMap (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : orthogonalDerived Q →* omegaProj hQ :=
  MonoidHom.codRestrict ((toProj Q).comp (orthogonalDerived Q).subtype) (omegaProj hQ) (fun x =>
    (mem_omegaProj_iff hQ).mpr
      ⟨x.val, by rw [omegaGroup_eq_commutator hQ h2]; exact x.property, rfl⟩)

theorem fa8ClassMap_surjective (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : Function.Surjective (fa8ClassMap hQ h2) := by
  rintro ⟨w, hw⟩
  obtain ⟨t, ht, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  rw [omegaGroup_eq_commutator hQ h2] at ht
  exact ⟨⟨t, ht⟩, Subtype.ext rfl⟩

theorem fa8ClassMap_ker (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (fa8ClassMap hQ h2).ker = (scalarSigns Q).subgroupOf (orthogonalDerived Q) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, fa8_scalarSigns_eq_piGroup]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

@[expose] noncomputable def fa8ProjDerivedEquiv (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) : projectiveDerived Q ≃* omegaProj hQ :=
  (QuotientGroup.quotientMulEquivOfEq (fa8ClassMap_ker hQ h2).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fa8ClassMap_surjective hQ h2))

theorem fa8ProjDerivedEquiv_mk (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (x : orthogonalDerived Q) :
    ((fa8ProjDerivedEquiv hQ h2
      (QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) x) : omegaProj hQ) :
        ProjOrth Q) = toProj Q x.val :=
  rfl

theorem fa8ProjDerivedEquiv_projectiveConjugation (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (A : V ≃ₗ[ZMod 3] V) (μ : (ZMod 3)ˣ)
    (hsim : ∀ x : V, Q (A x) = (μ : ZMod 3) * Q x) (y : projectiveDerived Q) :
    fa8ProjDerivedEquiv hQ h2 (projectiveConjugation Q A μ hsim y) =
      ffSimOmegaAct hQ h2 (QuotientGroup.mk (⟨A, μ, hsim⟩ : simGroup Q))
        (fa8ProjDerivedEquiv hQ h2 y) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
  apply Subtype.ext
  rw [projectiveConjugation_mk, fa8ProjDerivedEquiv_mk, coe_ffSimOmegaAct,
    fa8ProjDerivedEquiv_mk, projSimAct_mk, projActAux_toProj]
  congr 1

end CFSG.OddStandard.SmallF3.Omega
