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

@[expose] def IsOmegaStar (X : Type) [Group X] (n : ℕ) (ε : ℤˣ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧ Nonempty (X ≃* omegaProj hQ)

@[expose] def IsOmegaCover (X : Type) [Group X] (n : ℕ) (ε : ℤˣ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧ Nonempty (X ≃* omegaGroup hQ)

private lemma orthogonalGroupCongr_map_omegaGroup (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    (omegaGroup hQ).map (orthogonalGroupCongr e).toMonoidHom = omegaGroup hQ' := by
  have h2' : 2 ≤ Module.finrank (ZMod 3) V' := by
    rw [← e.toLinearEquiv.finrank_eq]; exact h2
  rw [omegaGroup_eq_commutator hQ h2, omegaGroup_eq_commutator hQ' h2',
    commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (orthogonalGroupCongr e).surjective]

private lemma orthogonalGroupCongr_map_piGroup (e : Q.IsometryEquiv Q') :
    (piGroup Q).map (orthogonalGroupCongr e).toMonoidHom = piGroup Q' := by
  have hpi : orthogonalGroupCongr e (piOrth Q) = piOrth Q' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    rw [coe_orthogonalGroupCongr_apply, coe_piOrth_apply, map_neg,
      LinearEquiv.apply_symm_apply, coe_piOrth_apply]
  rw [piGroup, piGroup, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hpi

theorem nonempty_omegaGroup_mulEquiv (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Nonempty (omegaGroup hQ ≃* omegaGroup hQ') :=
  ⟨(MulEquiv.subgroupMap (orthogonalGroupCongr e) (omegaGroup hQ)).trans
    (MulEquiv.subgroupCongr (orthogonalGroupCongr_map_omegaGroup hQ hQ' e h2))⟩

theorem nonempty_omegaProj_mulEquiv (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (e : Q.IsometryEquiv Q') (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Nonempty (omegaProj hQ ≃* omegaProj hQ') := by
  have hmap := orthogonalGroupCongr_map_omegaGroup hQ hQ' e h2
  have hpi := orthogonalGroupCongr_map_piGroup (Q := Q) (Q' := Q') e
  let ψ : ProjOrth Q ≃* ProjOrth Q' :=
    QuotientGroup.congr (piGroup Q) (piGroup Q') (orthogonalGroupCongr e) hpi
  have hcomp : ψ.toMonoidHom.comp (toProj Q) =
      (toProj Q').comp (orthogonalGroupCongr e).toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk' (piGroup Q) (piGroup Q') (orthogonalGroupCongr e) hpi x
  have hproj : (omegaProj hQ).map ψ.toMonoidHom = omegaProj hQ' := by
    rw [omegaProj, omegaProj, Subgroup.map_map, ← hmap, Subgroup.map_map, hcomp]
  exact ⟨(MulEquiv.subgroupMap ψ (omegaProj hQ)).trans (MulEquiv.subgroupCongr hproj)⟩

theorem IsOmegaStar.nonempty_equiv {X : Type} [Group X] {n : ℕ} {ε : ℤˣ} (h : IsOmegaStar X n ε)
    (hn : 2 ≤ n) (hQ' : Q'.Nondegenerate) (hdim : Module.finrank (ZMod 3) V' = n)
    (hs : quadSign Q' = ε) : Nonempty (X ≃* omegaProj hQ') := by
  obtain ⟨V₀, i1, i2, i3, Q₀, hQ₀, hdim₀, hs₀, ⟨f⟩⟩ := h
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ₀ hQ' (hdim₀.trans hdim.symm) (hs₀.trans hs.symm)
  obtain ⟨g⟩ := nonempty_omegaProj_mulEquiv hQ₀ hQ' e (by omega)
  exact ⟨f.trans g⟩

theorem IsOmegaCover.nonempty_equiv {X : Type} [Group X] {n : ℕ} {ε : ℤˣ}
    (h : IsOmegaCover X n ε) (hn : 2 ≤ n) (hQ' : Q'.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V' = n) (hs : quadSign Q' = ε) :
    Nonempty (X ≃* omegaGroup hQ') := by
  obtain ⟨V₀, i1, i2, i3, Q₀, hQ₀, hdim₀, hs₀, ⟨f⟩⟩ := h
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ₀ hQ' (hdim₀.trans hdim.symm) (hs₀.trans hs.symm)
  obtain ⟨g⟩ := nonempty_omegaGroup_mulEquiv hQ₀ hQ' e (by omega)
  exact ⟨f.trans g⟩

end CFSG.OddStandard.SmallF3.Omega
