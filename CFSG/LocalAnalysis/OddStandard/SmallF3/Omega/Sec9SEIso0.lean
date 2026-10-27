module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  [AddCommGroup V'] [Module (ZMod 3) V'] [FiniteDimensional (ZMod 3) V']
  {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}

theorem isoO_map_omegaGroup (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (omegaGroup hQ).map (orthogonalGroupCongr e).toMonoidHom = omegaGroup hQ' := by
  have h2' : 2 ≤ Module.finrank (ZMod 3) V' := by
    rw [← e.toLinearEquiv.finrank_eq]; exact h2
  rw [omegaGroup_eq_commutator hQ h2, omegaGroup_eq_commutator hQ' h2',
    commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (orthogonalGroupCongr e).surjective]

theorem isoO_map_piGroup (e : Q.IsometryEquiv Q') :
    (piGroup Q).map (orthogonalGroupCongr e).toMonoidHom = piGroup Q' := by
  have hpi : orthogonalGroupCongr e (piOrth Q) = piOrth Q' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    rw [coe_orthogonalGroupCongr_apply, coe_piOrth_apply, map_neg,
      LinearEquiv.apply_symm_apply, coe_piOrth_apply]
  rw [piGroup, piGroup, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hpi

@[expose] noncomputable def projOrthCongr (e : Q.IsometryEquiv Q') : ProjOrth Q ≃* ProjOrth Q' :=
  QuotientGroup.congr (piGroup Q) (piGroup Q') (orthogonalGroupCongr e) (isoO_map_piGroup e)

theorem projOrthCongr_toProj (e : Q.IsometryEquiv Q') (t : OGroup Q) :
    projOrthCongr e (toProj Q t) = toProj Q' (orthogonalGroupCongr e t) :=
  QuotientGroup.congr_mk' (piGroup Q) (piGroup Q') (orthogonalGroupCongr e) (isoO_map_piGroup e) t

theorem map_omegaProj_projOrthCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (omegaProj hQ).map (projOrthCongr e).toMonoidHom = omegaProj hQ' := by
  have hmap := isoO_map_omegaGroup hQ hQ' e h2
  have hcomp : (projOrthCongr e).toMonoidHom.comp (toProj Q) =
      (toProj Q').comp (orthogonalGroupCongr e).toMonoidHom := by
    ext x
    exact projOrthCongr_toProj e x
  rw [omegaProj, omegaProj, Subgroup.map_map, ← hmap, Subgroup.map_map, hcomp]

@[expose] noncomputable def omegaProjCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    omegaProj hQ ≃* omegaProj hQ' :=
  (MulEquiv.subgroupMap (projOrthCongr e) (omegaProj hQ)).trans
    (MulEquiv.subgroupCongr (map_omegaProj_projOrthCongr hQ hQ' e h2))

theorem coe_omegaProjCongr (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) (a : omegaProj hQ) :
    ((omegaProjCongr hQ hQ' e h2 a : omegaProj hQ') : ProjOrth Q') =
      projOrthCongr e (a : ProjOrth Q) :=
  rfl

end CFSG.OddStandard.SmallF3.Omega
